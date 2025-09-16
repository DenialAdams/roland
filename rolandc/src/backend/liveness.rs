use bitvec::prelude::*;
use indexmap::{IndexMap, IndexSet};

use super::linearize::{Cfg, CfgInstruction};
use crate::backend::linearize::post_order;
use crate::constant_folding::expression_could_have_side_effects;
use crate::parse::{Expression, ExpressionId, ExpressionPool, ProcedureBody, UnOp, VariableId};
use crate::type_data::ExpressionType;

#[derive(Clone)]
struct LivenessState {
   live_in: BitBox,
   live_out: BitBox,
   gen_: BitBox,
   kill: BitBox,
   gen_address_escaped: BitBox,
   address_escaped_out: BitBox,
   address_escaped_out_changed: bool,
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
   cfg: &mut Cfg,
   ast: &ExpressionPool,
) -> IndexMap<ProgramIndex, BitBox> {
   let mut all_liveness: IndexMap<ProgramIndex, BitBox> = IndexMap::new();
   let mut all_address_escaped: IndexMap<ProgramIndex, BitBox> = IndexMap::new();
   let mut current_live_variables = BitVec::new();
   let mut current_address_escaped = bitvec![0; procedure_vars.len()];

   // Dataflow Analyis on the CFG
   let mut state = vec![
      LivenessState {
         live_in: bitbox![0; procedure_vars.len()],
         live_out: bitbox![0; procedure_vars.len()],
         gen_: bitbox![0; procedure_vars.len()],
         kill: bitbox![0; procedure_vars.len()],
         gen_address_escaped: bitbox![0; procedure_vars.len()],
         address_escaped_out: bitbox![0; procedure_vars.len()],
         address_escaped_out_changed: false,
      };
      cfg.bbs.len()
   ];

   // we want to go backwards, which is post_order, but since we are popping we must reverse
   let mut worklist: IndexSet<usize> = post_order(cfg).into_iter().rev().collect();

   while !worklist.is_empty() {
      // Setup
      for i in worklist.iter() {
         let bb = &cfg.bbs[*i];
         let s = &mut state[*i];
         // We need to reset s.address_escaped_out (since we may have just eliminated the escaping of an address)
         // so that it's cleanly recomputed from gen. otherwise, a block with itself as a predecessor would
         // never be able to lose a bit (so this only matters for loops.)
         // because we are filling address_escaped_out with false, we must conservatively mark it as changed,
         // otherwise if went from N vars address taken => 0 vars adress taken we wouldn't know to re-propagate forward
         // TODO: doesn't above reasoning also apply to live_out? should we be clearing that? i can't make an example.
         s.address_escaped_out_changed = s.address_escaped_out.any();
         s.address_escaped_out.fill(false);
         s.gen_.fill(false);
         s.kill.fill(false);
         s.gen_address_escaped.fill(false);
         for instruction in bb.instructions.iter().rev() {
            match instruction {
               CfgInstruction::Assignment(lhs, rhs) => {
                  if let Expression::Variable(v) = ast[*lhs].expression
                     && let Some(di) = procedure_vars.get_index_of(&v)
                  {
                     s.gen_.set(di, false);
                     s.kill.set(di, true);
                  } else {
                     gen_for_expr(*lhs, &mut s.gen_, &mut s.kill, ast, procedure_vars);
                     mark_address_escaped_expr(*lhs, &mut s.gen_address_escaped, ast, procedure_vars);
                  }
                  gen_for_expr(*rhs, &mut s.gen_, &mut s.kill, ast, procedure_vars);
                  if let Some(di) = mark_address_escaped_expr(*rhs, &mut s.gen_address_escaped, ast, procedure_vars) {
                     s.gen_address_escaped.set(di, true);
                  }
               }
               CfgInstruction::Expression(expr)
               | CfgInstruction::Return(expr)
               | CfgInstruction::ConditionalJump(expr, _, _) => {
                  gen_for_expr(*expr, &mut s.gen_, &mut s.kill, ast, procedure_vars);
                  mark_address_escaped_expr(*expr, &mut s.gen_address_escaped, ast, procedure_vars);
               }
               CfgInstruction::Nop | CfgInstruction::Jump(_) => (),
            }
         }
      }

      // get a forwards worklist, then compute address_escaped for each block
      let mut address_escaped_worklist: IndexSet<usize> = worklist.iter().rev().copied().collect();
      while let Some(block_idx) = address_escaped_worklist.pop() {
         let mut new = state[block_idx].gen_address_escaped.clone();
         for p in cfg.bbs[block_idx].predecessors.iter().copied() {
            new |= &state[p].address_escaped_out;
         }
         state[block_idx].address_escaped_out_changed |= new != state[block_idx].address_escaped_out;
         if state[block_idx].address_escaped_out_changed {
            state[block_idx].address_escaped_out = new;
            state[block_idx].address_escaped_out_changed = false;
            address_escaped_worklist.extend(cfg.bbs[block_idx].successors().iter().copied());
         }
      }

      // back to the main attraction. iterative fixed point to build liveness for the CFG.
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
            let old_live_in = std::mem::replace(&mut s.live_in, s.gen_.clone());

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

      // Construct the final results (per-statement)
      // We may perform dead code elimination, putting blocks back onto the worklist
      for (rpo_index, node_id) in post_order(cfg).iter().copied().rev().enumerate() {
         let s = &state[node_id];

         current_live_variables.clear();
         current_live_variables.extend_from_bitslice(&s.live_out);

         current_address_escaped.fill(false);
         for p in cfg.bbs[node_id].predecessors.iter().copied() {
            current_address_escaped |= &state[p].address_escaped_out;
         }

         let bb = &mut cfg.bbs[node_id];
         all_liveness.reserve(bb.instructions.len());
         all_address_escaped.reserve(bb.instructions.len());

         // Set address taken for all points in this block
         for (i, instruction) in bb.instructions.iter().enumerate() {
            match instruction {
               CfgInstruction::Assignment(lhs, rhs) => {
                  if let Expression::Variable(v) = ast[*lhs].expression
                     && let Some(_) = procedure_vars.get_index_of(&v)
                  {
                     // nothing
                  } else {
                     mark_address_escaped_expr(*lhs, &mut current_address_escaped, ast, procedure_vars);
                  }
                  if let Some(di) = mark_address_escaped_expr(*rhs, &mut current_address_escaped, ast, procedure_vars) {
                     current_address_escaped.set(di, true);
                  }
               }
               CfgInstruction::Expression(expr)
               | CfgInstruction::Return(expr)
               | CfgInstruction::ConditionalJump(expr, _, _) => {
                  mark_address_escaped_expr(*expr, &mut current_address_escaped, ast, procedure_vars);
               }
               _ => (),
            }
            all_address_escaped.insert(
               ProgramIndex(rpo_index, i),
               current_address_escaped.clone().into_boxed_bitslice(),
            );
         }

         // Set liveness for all points in this block
         for (i, instruction) in bb.instructions.iter_mut().enumerate().rev() {
            let here = ProgramIndex(rpo_index, i);
            current_live_variables |= &all_address_escaped[&here];
            match instruction {
               CfgInstruction::Assignment(lhs, rhs) => {
                  let lhs = *lhs;
                  let rhs = *rhs;
                  if let Expression::Variable(v) = ast[lhs].expression
                     && let Some(di) = procedure_vars.get_index_of(&v)
                  {
                     if !current_live_variables[di] {
                        // never read. nuke the assignment. we do this as we are processing so that we avoid marking anything in the RHS as live if we don't have to
                        // note that this is not strictly an optimization!
                        // this is needed for correctness, because
                        //   1) register allocation assumes that no overlapping ranges = good to merge
                        //   2) a dead write is not considered to be part of that range
                        //   3) if executed, that dead write could affect the merged variable
                        if expression_could_have_side_effects(rhs, ast) {
                           *instruction = CfgInstruction::Expression(rhs);
                        } else {
                           *instruction = CfgInstruction::Nop;
                           // Since the RHS is now dead, the liveness results may be affected, so we push this node back onto the worklist
                           worklist.insert(node_id);
                        }
                     }
                     current_live_variables.set(di, false);
                  } else {
                     update_live_variables_for_expr(lhs, &mut current_live_variables, ast, procedure_vars);
                  }
                  update_live_variables_for_expr(rhs, &mut current_live_variables, ast, procedure_vars);
               }
               CfgInstruction::Expression(expr)
               | CfgInstruction::Return(expr)
               | CfgInstruction::ConditionalJump(expr, _, _) => {
                  update_live_variables_for_expr(*expr, &mut current_live_variables, ast, procedure_vars);
               }
               _ => (),
            }
            all_liveness.insert(here, current_live_variables.clone().into_boxed_bitslice());
         }
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
   gen_: &mut BitSlice,
   kill: &mut BitSlice,
   ast: &ExpressionPool,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
) {
   match &ast[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         gen_for_expr(*proc_expr, gen_, kill, ast, procedure_vars);

         for val in args.iter().map(|x| x.expr) {
            gen_for_expr(val, gen_, kill, ast, procedure_vars);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            gen_for_expr(val, gen_, kill, ast, procedure_vars);
         }
      }
      Expression::ArrayIndex { array: a, index: b } | Expression::BinaryOperator { lhs: a, rhs: b, .. } => {
         gen_for_expr(*a, gen_, kill, ast, procedure_vars);
         gen_for_expr(*b, gen_, kill, ast, procedure_vars);
      }
      Expression::IfX(a, b, c) => {
         gen_for_expr(*a, gen_, kill, ast, procedure_vars);
         gen_for_expr(*b, gen_, kill, ast, procedure_vars);
         gen_for_expr(*c, gen_, kill, ast, procedure_vars);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            gen_for_expr(*expr, gen_, kill, ast, procedure_vars);
         }
      }
      Expression::FieldAccess(_, expr) | Expression::Cast { expr, .. } | Expression::UnaryOperator(_, expr) => {
         gen_for_expr(*expr, gen_, kill, ast, procedure_vars);
      }
      Expression::Variable(var) => {
         if let Some(di) = procedure_vars.get_index_of(var) {
            gen_.set(di, true);
            kill.set(di, false);
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

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ProgramIndex(pub usize, pub usize); // (RPO basic block position, instruction inside of block)

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct LiveInterval {
   pub begin: ProgramIndex,
   pub end: ProgramIndex,
}

fn mark_address_escaped_expr(
   in_expr: ExpressionId,
   address_escaped: &mut BitSlice,
   ast: &ExpressionPool,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
) -> Option<usize> {
   match &ast[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_address_escaped_expr(*proc_expr, address_escaped, ast, procedure_vars);

         for val in args.iter().map(|x| x.expr) {
            if let Some(di) = mark_address_escaped_expr(val, address_escaped, ast, procedure_vars) {
               // The caller could do anything with the address, so give up
               address_escaped.set(di, true);
            }
         }

         None
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         let a = mark_address_escaped_expr(*lhs, address_escaped, ast, procedure_vars);
         let b = mark_address_escaped_expr(*rhs, address_escaped, ast, procedure_vars);

         if let Some(di_a) = a && let Some(di_b) = b {
            // give up
            address_escaped.set(di_a, true);
            address_escaped.set(di_b, true);
            None
         } else {
            a.or(b)
         }
      }
      Expression::IfX(a, b, c) => {
         let ea = mark_address_escaped_expr(*a, address_escaped, ast, procedure_vars);
         let eb = mark_address_escaped_expr(*b, address_escaped, ast, procedure_vars);
         let ec = mark_address_escaped_expr(*c, address_escaped, ast, procedure_vars);

         if usize::from(ea.is_some()) + usize::from(eb.is_some()) + usize::from(ec.is_some()) > 1 {
            if let Some(di) = ea {
               mark_escaped(di);
            }
            if let Some(di) = eb {
               mark_escaped(di);
            }
            if let Some(di) = ec {
               mark_escaped(di);
            }
            return None;
         }

         ea.or(eb).or(ec)
      }
      Expression::Cast { expr, .. } => {
         mark_address_escaped_expr(*expr, address_escaped, ast, procedure_vars)
      }
      Expression::UnaryOperator(op, expr) => {
         mark_address_escaped_expr(*expr, address_escaped, ast, procedure_vars).filter(|_| *op != UnOp::Dereference)
      }
      Expression::Variable(v) => procedure_vars.get_index_of(v),
      Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => None,
      Expression::ArrayIndex { .. }
      | Expression::FieldAccess(_, _)
      | Expression::ArrayLiteral(_)
      | Expression::StructLiteral(_, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}
