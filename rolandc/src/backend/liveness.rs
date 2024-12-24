use bitvec::prelude::*;
use indexmap::{IndexMap, IndexSet};

use super::linearize::{Cfg, CfgInstruction};
use crate::backend::linearize::post_order;
use crate::constant_folding::expression_could_have_side_effects;
use crate::parse::{Expression, ExpressionId, ExpressionPool, ProcedureBody, VariableId};
use crate::type_data::ExpressionType;

#[derive(Clone)]
struct LivenessState {
   live_in: BitBox,
   live_out: BitBox,
   gen: BitBox,
   kill: BitBox,
}

pub fn kill_dead_assignments(
   body: &mut ProcedureBody,
   liveness_results: &IndexMap<ProgramIndex, BitBox>,
   ast: &ExpressionPool,
) {
   // note that this is not strictly an optimization!
   // this is needed for correctness, because
   //   1) register allocation assumes that no overlapping ranges = good to merge
   //   2) a dead write is not considered to be part of that range
   //   3) if executed, that dead write could affect the merged variable
   for (rpo_pos, bb_index) in post_order(&body.cfg).iter().copied().rev().enumerate() {
      for (bb_pos, instr) in body.cfg.bbs[bb_index].instructions.iter_mut().enumerate() {
         let CfgInstruction::Assignment(lhs, rhs) = *instr else {
            continue;
         };
         let Expression::Variable(l_var) = ast[lhs].expression else {
            continue;
         };
         let Some(local_index) = body.locals.get_index_of(&l_var) else {
            // variable not modeled by the analysis - i.e. static
            continue;
         };
         // check to see if the variable is live on the following statement
         // (the variable will necessarily not be live on the statement that assigns it) 
         // (there is always a next instruction in the block, because a block must be terminated with a jump)
         let next_pos = ProgramIndex(rpo_pos, bb_pos + 1);
         if liveness_results[&next_pos][local_index] {
            continue;
         }
         *instr = if expression_could_have_side_effects(rhs, ast) {
            CfgInstruction::Expression(rhs)
         } else {
            CfgInstruction::Nop
         };
      }
   }
}

#[must_use]
pub fn compute_live_intervals(
   body: &ProcedureBody,
   proc_liveness: &IndexMap<ProgramIndex, BitBox>,
) -> IndexMap<VariableId, LiveInterval> {
   let mut live_intervals: IndexMap<VariableId, LiveInterval> = IndexMap::with_capacity(body.locals.len());
   for (pi, live_vars) in proc_liveness.iter() {
      for local_index in live_vars.iter_ones() {
         let var = body.locals.get_index(local_index).map(|x| *x.0).unwrap();
         if let Some(existing_range) = live_intervals.get_mut(&var) {
            existing_range.begin = std::cmp::min(existing_range.begin, *pi);
            existing_range.end = std::cmp::max(existing_range.end, *pi);
         } else {
            live_intervals.insert(var, LiveInterval { begin: *pi, end: *pi });
         }
      }
   }
   live_intervals.sort_unstable_by(|_, v1, _, v2| v1.begin.cmp(&v2.begin));

   live_intervals
}

#[must_use]
pub fn liveness(
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &Cfg,
   ast: &ExpressionPool,
) -> IndexMap<ProgramIndex, BitBox> {
   // Dataflow Analyis on the CFG
   let mut state = vec![
      LivenessState {
         live_in: bitbox![0; procedure_vars.len()],
         live_out: bitbox![0; procedure_vars.len()],
         gen: bitbox![0; procedure_vars.len()],
         kill: bitbox![0; procedure_vars.len()],
      };
      cfg.bbs.len()
   ];

   // Setup
   for (i, bb) in cfg.bbs.iter().enumerate() {
      let s = &mut state[i];
      for instruction in bb.instructions.iter().rev() {
         match instruction {
            CfgInstruction::Assignment(lhs, rhs) => {
               gen_for_expr(*lhs, &mut s.gen, &mut s.kill, ast, procedure_vars);
               if let Expression::Variable(v) = ast[*lhs].expression {
                  if let Some(di) = procedure_vars.get_index_of(&v) {
                     s.gen.set(di, false);
                     s.kill.set(di, true);
                  }
               }
               gen_for_expr(*rhs, &mut s.gen, &mut s.kill, ast, procedure_vars);
            }
            CfgInstruction::Expression(expr)
            | CfgInstruction::Return(expr)
            | CfgInstruction::ConditionalJump(expr, _, _) => {
               gen_for_expr(*expr, &mut s.gen, &mut s.kill, ast, procedure_vars);
            }
            CfgInstruction::Nop | CfgInstruction::Jump(_) => (),
         }
      }
   }

   // we want to go backwards, which is post_order, but since we are popping we must reverse
   let mut worklist: IndexSet<usize> = post_order(cfg).into_iter().rev().collect();
   while let Some(node_id) = worklist.pop() {
      // Update live_out
      {
         let mut new_live_out = std::mem::replace(&mut state[node_id].live_out, bitbox![0; 0]);
         new_live_out.fill(false);
         for successor in cfg.bbs[node_id].successors() {
            let successor_s = &state[successor];
            new_live_out |= &successor_s.live_in;
         }
         state[node_id].live_out = new_live_out;
      }

      // Update live_in
      {
         let s = &mut state[node_id];
         let old_live_in = std::mem::replace(&mut s.live_in, s.gen.clone());

         // s.live_in |= s.live_out & !s.kill;
         for ((lhs, rhs), mut dst) in s
            .live_out
            .iter()
            .by_vals()
            .zip(s.kill.iter().by_vals())
            .zip(s.live_in.iter_mut())
         {
            *dst |= lhs & !rhs;
         }

         if old_live_in != s.live_in {
            worklist.extend(&cfg.bbs[node_id].predecessors);
         }
      }
   }

   // Construct the final results
   let mut all_liveness: IndexMap<ProgramIndex, BitBox> = IndexMap::new();
   let mut current_live_variables = BitVec::new();
   for (rpo_index, node_id) in post_order(cfg).iter().copied().rev().enumerate() {
      let bb = &cfg.bbs[node_id];
      let s = &state[node_id];
      current_live_variables.clear();
      current_live_variables.extend_from_bitslice(&s.live_out);
      all_liveness.reserve(bb.instructions.len());
      for (i, instruction) in bb.instructions.iter().enumerate().rev() {
         match instruction {
            CfgInstruction::Assignment(lhs, rhs) => {
               update_live_variables_for_expr(*lhs, &mut current_live_variables, ast, procedure_vars);
               if let Expression::Variable(v) = ast[*lhs].expression {
                  if let Some(di) = procedure_vars.get_index_of(&v) {
                     current_live_variables.set(di, false);
                  }
               }
               update_live_variables_for_expr(*rhs, &mut current_live_variables, ast, procedure_vars);
            }
            CfgInstruction::Expression(expr)
            | CfgInstruction::Return(expr)
            | CfgInstruction::ConditionalJump(expr, _, _) => {
               update_live_variables_for_expr(*expr, &mut current_live_variables, ast, procedure_vars);
            }
            _ => (),
         }
         all_liveness.insert(
            ProgramIndex(rpo_index, i),
            current_live_variables.clone().into_boxed_bitslice(),
         );
      }
   }

   all_liveness
}

fn update_live_variables_for_expr(
   expr: ExpressionId,
   current_live_variables: &mut BitSlice,
   ast: &ExpressionPool,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
) {
   match &ast[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         update_live_variables_for_expr(*proc_expr, current_live_variables, ast, procedure_vars);

         for val in args.iter().map(|x| x.expr) {
            update_live_variables_for_expr(val, current_live_variables, ast, procedure_vars);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            update_live_variables_for_expr(val, current_live_variables, ast, procedure_vars);
         }
      }
      Expression::ArrayIndex { array, index } => {
         update_live_variables_for_expr(*array, current_live_variables, ast, procedure_vars);
         update_live_variables_for_expr(*index, current_live_variables, ast, procedure_vars);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         update_live_variables_for_expr(*lhs, current_live_variables, ast, procedure_vars);
         update_live_variables_for_expr(*rhs, current_live_variables, ast, procedure_vars);
      }
      Expression::IfX(a, b, c) => {
         update_live_variables_for_expr(*a, current_live_variables, ast, procedure_vars);
         update_live_variables_for_expr(*b, current_live_variables, ast, procedure_vars);
         update_live_variables_for_expr(*c, current_live_variables, ast, procedure_vars);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            update_live_variables_for_expr(*expr, current_live_variables, ast, procedure_vars);
         }
      }
      Expression::FieldAccess(_, expr) | Expression::Cast { expr, .. } | Expression::UnaryOperator(_, expr) => {
         update_live_variables_for_expr(*expr, current_live_variables, ast, procedure_vars);
      }
      Expression::Variable(var) => {
         if let Some(di) = procedure_vars.get_index_of(var) {
            current_live_variables.set(di, true);
         }
      }
      Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => (),
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}

fn gen_for_expr(
   expr: ExpressionId,
   gen: &mut BitSlice,
   kill: &mut BitSlice,
   ast: &ExpressionPool,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
) {
   match &ast[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         gen_for_expr(*proc_expr, gen, kill, ast, procedure_vars);

         for val in args.iter().map(|x| x.expr) {
            gen_for_expr(val, gen, kill, ast, procedure_vars);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            gen_for_expr(val, gen, kill, ast, procedure_vars);
         }
      }
      Expression::ArrayIndex { array: a, index: b } | Expression::BinaryOperator { lhs: a, rhs: b, .. } => {
         gen_for_expr(*a, gen, kill, ast, procedure_vars);
         gen_for_expr(*b, gen, kill, ast, procedure_vars);
      }
      Expression::IfX(a, b, c) => {
         gen_for_expr(*a, gen, kill, ast, procedure_vars);
         gen_for_expr(*b, gen, kill, ast, procedure_vars);
         gen_for_expr(*c, gen, kill, ast, procedure_vars);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            gen_for_expr(*expr, gen, kill, ast, procedure_vars);
         }
      }
      Expression::FieldAccess(_, expr) | Expression::Cast { expr, .. } | Expression::UnaryOperator(_, expr) => {
         gen_for_expr(*expr, gen, kill, ast, procedure_vars);
      }
      Expression::Variable(var) => {
         if let Some(di) = procedure_vars.get_index_of(var) {
            gen.set(di, true);
            kill.set(di, false);
         };
      }
      Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => (),
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ProgramIndex(pub usize, pub usize); // (RPO basic block position, instruction inside of block)

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct LiveInterval {
   pub begin: ProgramIndex,
   pub end: ProgramIndex,
}
