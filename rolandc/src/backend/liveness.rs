use bitvec::prelude::*;
use indexmap::{IndexMap, IndexSet};

use super::linearize::{Cfg, CfgInstruction};
use crate::BaseTarget;
use crate::backend::linearize::post_order;
use crate::backend::pointer_analysis::{PointerAnalysisResult, PointsTo, PointsToOwned};
use crate::constant_folding::expression_could_have_side_effects;
use crate::parse::{BinOp, Expression, ExpressionId, ExpressionPool, UnOp, UserDefinedTypeInfo, VariableId};
use crate::size_info::sizeof_type_mem;
use crate::type_data::ExpressionType;

#[derive(Clone)]
struct LivenessState {
   live_in: BitBox,
   live_out: BitBox,
   gen_: BitBox,
   kill: BitBox,
   gen_address_taken: BitBox,
   address_taken_out: BitBox,
}

fn extend_live_interval(intervals: &mut [Option<LiveInterval>], local_index: usize, here: ProgramIndex) {
   if let Some(interval) = &mut intervals[local_index] {
      interval.begin = std::cmp::min(interval.begin, here);
      interval.end = std::cmp::max(interval.end, here);
   } else {
      intervals[local_index] = Some(LiveInterval { begin: here, end: here });
   }
}

#[must_use]
pub fn compute_live_intervals(
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &mut Cfg,
   ast: &ExpressionPool,
   target: BaseTarget,
   udt: &UserDefinedTypeInfo,
   pointer_analysis_result: &PointerAnalysisResult,
   mut instruction_liveness: Option<&mut IndexMap<ProgramIndex, BitBox>>,
) -> IndexMap<VariableId, LiveInterval> {
   let mut dense_live_intervals: Vec<Option<LiveInterval>> = vec![None; procedure_vars.len()];
   let tail_bits = procedure_vars.len() % usize::BITS as usize;
   let tail_mask = if tail_bits == 0 {
      usize::MAX
   } else {
      usize::MAX >> (usize::BITS as usize - tail_bits)
   };
   let mut block_address_taken: BitVec = BitVec::new();
   // Keep each snapshot word-aligned, and reuse the storage across blocks and DCE iterations.
   let address_taken_stride = procedure_vars.len().next_multiple_of(usize::BITS as usize);
   let mut current_live_variables = BitVec::new();
   let mut current_address_taken = bitvec![0; procedure_vars.len()];
   let mut new_address_taken = bitbox![0; procedure_vars.len()];
   let mut visit_in_progress = bitbox![0; procedure_vars.len()];

   // Dataflow Analyis on the CFG
   let mut state = vec![
      LivenessState {
         live_in: bitbox![0; procedure_vars.len()],
         live_out: bitbox![0; procedure_vars.len()],
         gen_: bitbox![0; procedure_vars.len()],
         kill: bitbox![0; procedure_vars.len()],
         gen_address_taken: bitbox![0; procedure_vars.len()],
         address_taken_out: bitbox![0; procedure_vars.len()],
      };
      cfg.bbs.len()
   ];

   // DCE changes instructions but never the CFG edges, so this order stays valid.
   let block_order = post_order(cfg);
   // we want to go backwards, which is post_order, but since we are popping we must reverse
   let mut worklist: IndexSet<usize> = IndexSet::new();

   let mut keep_going = true;
   while keep_going {
      keep_going = false;
      // Discard ranges from earlier iterations: DCE can remove their last use.
      dense_live_intervals.fill(None);
      debug_assert!(worklist.is_empty());
      worklist.extend(block_order.iter().rev().copied());

      // Setup
      for i in worklist.iter() {
         let bb = &cfg.bbs[*i];
         let s = &mut state[*i];
         s.live_in.fill(false);
         s.live_out.fill(false);
         s.address_taken_out.fill(false);
         s.gen_.fill(false);
         s.kill.fill(false);
         s.gen_address_taken.fill(false);
         for instruction in bb.instructions.iter().rev() {
            match instruction {
               CfgInstruction::Assignment(lhs, rhs) => {
                  if let Expression::Variable(v) = ast[*lhs].expression
                     && let Some(di) = procedure_vars.get_index_of(&v)
                     && sizeof_type_mem(procedure_vars.get(&v).unwrap(), udt, target)
                        <= sizeof_type_mem(ast[*rhs].exp_type.as_ref().unwrap(), udt, target)
                  {
                     s.gen_.set(di, false);
                     s.kill.set(di, true);
                  } else {
                     gen_for_expr(*lhs, &mut s.gen_, &mut s.kill, ast, procedure_vars);
                     mark_address_taken_expr(*lhs, &mut s.gen_address_taken, ast, procedure_vars);
                  }
                  gen_for_expr(*rhs, &mut s.gen_, &mut s.kill, ast, procedure_vars);
                  if let Some(di) = mark_address_taken_expr(*rhs, &mut s.gen_address_taken, ast, procedure_vars) {
                     s.gen_address_taken.set(di, true);
                  }
               }
               CfgInstruction::Expression(expr)
               | CfgInstruction::Return(expr)
               | CfgInstruction::ConditionalJump(expr, _, _) => {
                  gen_for_expr(*expr, &mut s.gen_, &mut s.kill, ast, procedure_vars);
                  mark_address_taken_expr(*expr, &mut s.gen_address_taken, ast, procedure_vars);
               }
               CfgInstruction::Nop | CfgInstruction::Jump(_) => (),
            }
         }
      }

      // get a forwards worklist, then compute address_taken for each block
      let mut address_taken_worklist: IndexSet<usize> = worklist.iter().rev().copied().collect();
      while let Some(block_idx) = address_taken_worklist.pop() {
         new_address_taken.clone_from_bitslice(&state[block_idx].gen_address_taken);
         for p in cfg.bbs[block_idx].predecessors.iter().copied() {
            // These owned bitsets have equal lengths and start at bit zero.
            for (dst, src) in new_address_taken
               .as_raw_mut_slice()
               .iter_mut()
               .zip(state[p].address_taken_out.as_raw_slice())
            {
               *dst |= *src;
            }
         }
         if new_address_taken != state[block_idx].address_taken_out {
            std::mem::swap(&mut state[block_idx].address_taken_out, &mut new_address_taken);
            address_taken_worklist.extend(cfg.bbs[block_idx].successors().iter().copied());
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
               // These owned bitsets have equal lengths and start at bit zero.
               for (dst, src) in new_live_out
                  .as_raw_mut_slice()
                  .iter_mut()
                  .zip(successor_s.live_in.as_raw_slice())
               {
                  *dst |= *src;
               }
            }
            state[node_id].live_out = new_live_out;
         }

         // Update live_in
         {
            let s = &mut state[node_id];
            // We work on whole words so that this vectorizes
            let full_words = s.live_in.len() / usize::BITS as usize;
            let tail_bits = s.live_in.len() % usize::BITS as usize;
            let live_out = s.live_out.as_raw_slice();
            let kill = s.kill.as_raw_slice();
            let gen_ = s.gen_.as_raw_slice();
            let live_in = s.live_in.as_raw_mut_slice();
            let mut difference = 0;
            for (((out, kill), gen_), dst) in live_out
               .iter()
               .zip(s.kill.as_raw_slice())
               .zip(s.gen_.as_raw_slice())
               .zip(live_in[..full_words].iter_mut())
            {
               let next = gen_ | (out & !kill);
               difference |= next ^ *dst;
               *dst = next;
            }
            if tail_bits != 0 {
               let mask = usize::MAX >> (usize::BITS as usize - tail_bits);
               let next = (gen_[full_words] | (live_out[full_words] & !kill[full_words])) & mask;
               difference |= (next ^ live_in[full_words]) & mask;
               live_in[full_words] = next;
            }

            if difference != 0 {
               worklist.extend(&cfg.bbs[node_id].predecessors);
            }
         }
      }

      // Construct the final results (per-statement)
      // We may perform dead code elimination, putting blocks back onto the worklist
      for (rpo_index, node_id) in block_order.iter().copied().rev().enumerate() {
         let s = &state[node_id];

         current_live_variables.clear();
         current_live_variables.extend_from_bitslice(&s.live_out);

         current_address_taken.fill(false);
         for p in cfg.bbs[node_id].predecessors.iter().copied() {
            // These owned bitsets have equal lengths and start at bit zero.
            for (dst, src) in current_address_taken
               .as_raw_mut_slice()
               .iter_mut()
               .zip(state[p].address_taken_out.as_raw_slice())
            {
               *dst |= *src;
            }
         }

         let bb = &mut cfg.bbs[node_id];
         // The forwards fixed point is finished, so its scratch can track the previous
         // instruction's live set while we walk backwards through this block.
         let previous_live_variables = &mut new_address_taken;
         previous_live_variables.fill(false);
         if let Some(all_liveness) = instruction_liveness.as_deref_mut() {
            all_liveness.reserve(bb.instructions.len());
         }
         block_address_taken.resize(bb.instructions.len() * address_taken_stride, false);

         // Set address taken for all points in this block
         for (i, instruction) in bb.instructions.iter().enumerate() {
            match instruction {
               CfgInstruction::Assignment(lhs, rhs) => {
                  mark_address_taken_expr(*lhs, &mut current_address_taken, ast, procedure_vars);
                  if let Some(di) = mark_address_taken_expr(*rhs, &mut current_address_taken, ast, procedure_vars) {
                     current_address_taken.set(di, true);
                  }
               }
               CfgInstruction::Expression(expr)
               | CfgInstruction::Return(expr)
               | CfgInstruction::ConditionalJump(expr, _, _) => {
                  mark_address_taken_expr(*expr, &mut current_address_taken, ast, procedure_vars);
               }
               _ => (),
            }
            let start = i * address_taken_stride;
            block_address_taken[start..start + procedure_vars.len()].clone_from_bitslice(&current_address_taken);
         }

         // Set liveness for all points in this block
         for (i, instruction) in bb.instructions.iter_mut().enumerate().rev() {
            let here = ProgramIndex(rpo_index, i);

            match instruction {
               CfgInstruction::Assignment(lhs, rhs) => {
                  let lhs = *lhs;
                  let rhs = *rhs;
                  let mut deref_count: usize = 0;
                  let mut peeled_expr = lhs;
                  while let Expression::UnaryOperator(UnOp::Dereference, dt) = ast[peeled_expr].expression {
                     peeled_expr = dt;
                     deref_count += 1;
                  }
                  if let Expression::Variable(v) = ast[peeled_expr].expression
                     && let Some(di) = procedure_vars.get_index_of(&v)
                  {
                     let can_delete = if deref_count > 0 {
                        let mut points_to_transitive_closure: PointsToOwned =
                           pointer_analysis_result.points_to(di).to_owned();
                        'outer: for _ in (0..deref_count).skip(1) {
                           let PointsToOwned::Vars(ref mut closure_vars_in_progress) = points_to_transitive_closure
                           else {
                              break;
                           };
                           let og = closure_vars_in_progress.clone();
                           for di in og.iter_ones() {
                              match pointer_analysis_result.points_to(di) {
                                 PointsTo::Unknown => {
                                    points_to_transitive_closure = PointsToOwned::Unknown;
                                    break 'outer;
                                 }
                                 PointsTo::Vars(bit_slice) => {
                                    *closure_vars_in_progress |= bit_slice;
                                 }
                              }
                           }
                        }
                        match points_to_transitive_closure {
                           PointsToOwned::Unknown => false,
                           PointsToOwned::Vars(bb) => (bb & &current_live_variables).not_any(),
                        }
                     } else {
                        !current_live_variables[di]
                     };
                     if can_delete {
                        // never read. nuke the assignment.
                        // (we do this as we are processing so that we avoid marking anything in the RHS as live if we don't have to)
                        // note that removing the assignment is not strictly an optimization!
                        // this is needed for correctness, because
                        //   1) register allocation assumes that no overlapping ranges = good to merge
                        //   2) a dead write is not considered to be part of that range
                        //   3) if executed, that dead write could affect the merged variable
                        if expression_could_have_side_effects(rhs, ast) {
                           *instruction = CfgInstruction::Expression(rhs);
                        } else {
                           *instruction = CfgInstruction::Nop;
                           keep_going = true;
                        }
                     }
                     if deref_count == 0
                        && sizeof_type_mem(procedure_vars.get(&v).unwrap(), udt, target)
                           <= sizeof_type_mem(ast[rhs].exp_type.as_ref().unwrap(), udt, target)
                     {
                        current_live_variables.set(di, false);
                     } else if !can_delete {
                        update_live_variables_for_expr(lhs, &mut current_live_variables, ast, procedure_vars);
                     }
                  } else {
                     update_live_variables_for_expr(lhs, &mut current_live_variables, ast, procedure_vars);
                  }
                  // By skipping analysis of the RHS when possible, we avoid
                  // marking anything used in the RHS as live, letting us
                  // delete more in one iteration
                  if !matches!(instruction, CfgInstruction::Nop) {
                     update_live_variables_for_expr(rhs, &mut current_live_variables, ast, procedure_vars);
                  }
               }
               CfgInstruction::Expression(expr)
               | CfgInstruction::Return(expr)
               | CfgInstruction::ConditionalJump(expr, _, _) => {
                  update_live_variables_for_expr(*expr, &mut current_live_variables, ast, procedure_vars);
               }
               _ => (),
            }

            let start = i * address_taken_stride;
            for a_taken_address_var in block_address_taken[start..start + procedure_vars.len()].iter_ones() {
               fn var_is_effectively_live(
                  v: usize,
                  visit_in_progress: &mut BitSlice,
                  live_vars: &BitSlice,
                  pointer_analysis_result: &PointerAnalysisResult,
               ) -> bool {
                  if live_vars[v] {
                     // If a var was marked live, it's definitely live.
                     return true;
                  }

                  // Otherwise, a var is still live if a var pointing to it is effectively live

                  if visit_in_progress[v] {
                     // Indicates there is a cycle, X -> ... -> X
                     return false;
                  }
                  visit_in_progress.set(v, true);

                  let res = match pointer_analysis_result.who_points_to(v) {
                     PointsTo::Unknown => true,
                     PointsTo::Vars(bit_slice) => bit_slice
                        .iter_ones()
                        .any(|x| var_is_effectively_live(x, visit_in_progress, live_vars, pointer_analysis_result)),
                  };

                  visit_in_progress.set(v, false);

                  res
               }
               let el = var_is_effectively_live(
                  a_taken_address_var,
                  &mut visit_in_progress,
                  &current_live_variables,
                  pointer_analysis_result,
               );
               current_live_variables.set(a_taken_address_var, el);
            }

            // Once another DCE iteration is needed, these ranges will be discarded.
            if !keep_going {
               let words = current_live_variables.as_raw_slice();
               for (word_index, (&current, previous)) in
                  words.iter().zip(previous_live_variables.as_raw_mut_slice()).enumerate()
               {
                  let current = if word_index + 1 == words.len() {
                     current & tail_mask
                  } else {
                     current
                  };
                  let mut changes = current ^ *previous;
                  while changes != 0 {
                     let bit = changes.trailing_zeros() as usize;
                     let local_index = word_index * usize::BITS as usize + bit;
                     // A newly live variable ends here. One that just died started
                     // at the previous instruction, since this walk is backwards.
                     let point = if current & (1 << bit) != 0 {
                        here
                     } else {
                        ProgramIndex(rpo_index, i + 1)
                     };
                     extend_live_interval(&mut dense_live_intervals, local_index, point);
                     changes &= changes - 1;
                  }
                  *previous = current;
               }
            }

            if let Some(all_liveness) = instruction_liveness.as_deref_mut() {
               match all_liveness.entry(here) {
                  indexmap::map::Entry::Occupied(mut entry) => {
                     entry.get_mut().clone_from_bitslice(&current_live_variables);
                  }
                  indexmap::map::Entry::Vacant(entry) => {
                     entry.insert(current_live_variables.clone().into_boxed_bitslice());
                  }
               }
            }
         }
         if !keep_going && !bb.instructions.is_empty() {
            for local_index in current_live_variables.iter_ones() {
               extend_live_interval(&mut dense_live_intervals, local_index, ProgramIndex(rpo_index, 0));
            }
         }
      }
   }

   let mut live_intervals: IndexMap<VariableId, LiveInterval> = dense_live_intervals
      .into_iter()
      .enumerate()
      .filter_map(|(i, v)| v.map(|v| (*procedure_vars.get_index(i).unwrap().0, v)))
      .collect();
   live_intervals.sort_unstable_by(|_, v1, _, v2| v1.begin.cmp(&v2.begin));

   live_intervals
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

fn mark_address_taken_expr(
   in_expr: ExpressionId,
   address_taken: &mut BitSlice,
   ast: &ExpressionPool,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
) -> Option<usize> {
   match &ast[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_address_taken_expr(*proc_expr, address_taken, ast, procedure_vars);

         for val in args.iter().map(|x| x.expr) {
            if let Some(di) = mark_address_taken_expr(val, address_taken, ast, procedure_vars) {
               // The caller could do anything with the address, so give up
               address_taken.set(di, true);
            }
         }

         None
      }
      Expression::BinaryOperator { lhs, rhs, operator } => {
         let a = mark_address_taken_expr(*lhs, address_taken, ast, procedure_vars);
         let b = mark_address_taken_expr(*rhs, address_taken, ast, procedure_vars);

         match operator {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::Remainder
            | BinOp::BitwiseAnd
            | BinOp::BitwiseOr
            | BinOp::BitwiseXor
            | BinOp::BitwiseLeftShift
            | BinOp::BitwiseRightShift => (),
            BinOp::Equality
            | BinOp::NotEquality
            | BinOp::GreaterThan
            | BinOp::LessThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThanOrEqualTo
            | BinOp::LogicalAnd
            | BinOp::LogicalOr => return None,
         }

         if let Some(di_a) = a
            && let Some(di_b) = b
         {
            // a strange case like &a + &b, give up
            address_taken.set(di_a, true);
            address_taken.set(di_b, true);
            return None;
         }

         a.or(b)
      }
      Expression::IfX(a, b, c) => {
         mark_address_taken_expr(*a, address_taken, ast, procedure_vars);
         let eb = mark_address_taken_expr(*b, address_taken, ast, procedure_vars);
         let ec = mark_address_taken_expr(*c, address_taken, ast, procedure_vars);

         if eb.is_some() && ec.is_some() {
            if let Some(di) = eb {
               address_taken.set(di, true);
            }
            if let Some(di) = ec {
               address_taken.set(di, true);
            }
            return None;
         }

         eb.or(ec)
      }
      Expression::Cast { expr, .. } => mark_address_taken_expr(*expr, address_taken, ast, procedure_vars),
      Expression::UnaryOperator(op, expr) => {
         mark_address_taken_expr(*expr, address_taken, ast, procedure_vars).filter(|_| *op != UnOp::Dereference)
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
