use std::collections::{HashMap, HashSet};
use std::ops::Range;

use bitvec::prelude::*;
use indexmap::{IndexMap, IndexSet};
use rayon::iter::ParallelIterator;
use slotmap::SlotMap;

use crate::backend::linearize::{Cfg, CfgInstruction, post_order};
use crate::backend::liveness::ProgramIndex;
use crate::constant_folding::{self, FoldingContext, is_non_aggregate_const};
use crate::interner::Interner;
use crate::parse::{
   Expression, ExpressionId, ExpressionPool, ProcedureId, ProcedureNode, UnOp, UserDefinedTypeInfo, VariableId,
};
use crate::type_data::ExpressionType;
use crate::{BaseTarget, Program};

fn fold_expr_id(
   expr_id: ExpressionId,
   ast: &mut ExpressionPool,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
   global_exprs: &ExpressionPool,
   interner: &Interner,
   target: BaseTarget,
) {
   let mut fc = FoldingContext {
      procedures,
      user_defined_types,
      global_expressions: Some(global_exprs),
      const_replacements: None,
      current_proc_name: None,
      target,
      templated_types: &HashMap::new(),
   };
   constant_folding::try_fold_and_replace_expr(expr_id, &mut None, ast, &mut fc, interner);
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
enum ReachingVal {
   Const(ExpressionId),
   Var(VariableId),
}

fn find_reaching_val(x: Definition, body: &Cfg, rpo: &[usize], exprs: &ExpressionPool) -> Option<ReachingVal> {
   match x {
      Definition::DefinedAt(loc) => {
         let CfgInstruction::Assignment(_, rhs) = body.bbs[rpo[loc.0]].instructions[loc.1] else {
            return None;
         };
         let e = &exprs[rhs].expression;
         if is_non_aggregate_const(e) {
            Some(ReachingVal::Const(rhs))
         } else if let Expression::UnaryOperator(UnOp::Dereference, inner) = e {
            if let Expression::Variable(v) = exprs[*inner].expression {
               Some(ReachingVal::Var(v))
            } else {
               None
            }
         } else {
            None
         }
      }
      Definition::NoDefinitionInProc => None,
   }
}

fn propagate_vals(
   instruction: &CfgInstruction,
   ast: &mut ExpressionPool,
   get_reaching_val: &mut impl FnMut(VariableId, &ExpressionPool) -> Option<ReachingVal>,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
   global_exprs: &ExpressionPool,
   interner: &Interner,
   target: BaseTarget,
) {
   fn propagate_val_expr(
      e: ExpressionId,
      ast: &mut ExpressionPool,
      get_reaching_val: &mut impl FnMut(VariableId, &ExpressionPool) -> Option<ReachingVal>,
   ) -> bool {
      let mut propagated_const = false;
      let mut the_expression = std::mem::replace(&mut ast[e].expression, Expression::UnitLiteral);
      match &the_expression {
         Expression::UnaryOperator(UnOp::Dereference, child) => {
            if let Expression::Variable(v) = &ast[*child].expression {
               match get_reaching_val(*v, ast) {
                  Some(ReachingVal::Const(c)) => {
                     // only propagate consts when the type matches, or the type is bitwise identical (varies only in signed-ness)
                     let types_agreeable = match (ast[c].exp_type.as_ref().unwrap(), ast[e].exp_type.as_ref().unwrap())
                     {
                        (ExpressionType::Int(c_it), ExpressionType::Int(e_it)) => c_it.width == e_it.width,
                        (a, b) => a == b,
                     };
                     if types_agreeable {
                        the_expression = ast[c].expression.clone();
                        propagated_const = true;
                     }
                  }
                  Some(ReachingVal::Var(reaching_v)) => {
                     ast[*child].expression = Expression::Variable(reaching_v);
                  }
                  None => (),
               }
            } else {
               propagated_const |= propagate_val_expr(*child, ast, get_reaching_val);
            }
         }
         Expression::UnaryOperator(_, child) | Expression::Cast { expr: child, .. } => {
            propagated_const |= propagate_val_expr(*child, ast, get_reaching_val);
         }
         Expression::ArrayIndex { array, index } => {
            propagated_const |= propagate_val_expr(*array, ast, get_reaching_val);
            propagated_const |= propagate_val_expr(*index, ast, get_reaching_val);
         }
         Expression::ProcedureCall { proc_expr, args } => {
            propagated_const |= propagate_val_expr(*proc_expr, ast, get_reaching_val);
            for arg in args.iter() {
               propagated_const |= propagate_val_expr(arg.expr, ast, get_reaching_val);
            }
         }
         Expression::BinaryOperator { lhs, rhs, .. } => {
            propagated_const |= propagate_val_expr(*lhs, ast, get_reaching_val);
            propagated_const |= propagate_val_expr(*rhs, ast, get_reaching_val);
         }
         Expression::FieldAccess(_, base) => {
            propagated_const |= propagate_val_expr(*base, ast, get_reaching_val);
         }
         Expression::IfX(a, b, c) => {
            propagated_const |= propagate_val_expr(*a, ast, get_reaching_val);
            propagated_const |= propagate_val_expr(*b, ast, get_reaching_val);
            propagated_const |= propagate_val_expr(*c, ast, get_reaching_val);
         }
         Expression::Variable(_)
         | Expression::BoolLiteral(_)
         | Expression::StringLiteral(_)
         | Expression::IntLiteral { .. }
         | Expression::FloatLiteral(_)
         | Expression::UnitLiteral
         | Expression::EnumLiteral(_, _)
         | Expression::BoundFcnLiteral(_, _) => (),
         Expression::ArrayLiteral(_)
         | Expression::StructLiteral(_, _)
         | Expression::UnresolvedVariable(_)
         | Expression::UnresolvedStructLiteral(_, _, _)
         | Expression::UnresolvedEnumLiteral(_, _)
         | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      }
      ast[e].expression = the_expression;
      propagated_const
   }
   match instruction {
      CfgInstruction::Assignment(lhs, rhs) => {
         if propagate_val_expr(*lhs, ast, get_reaching_val) {
            fold_expr_id(
               *lhs,
               ast,
               procedures,
               user_defined_types,
               global_exprs,
               interner,
               target,
            );
         }
         if propagate_val_expr(*rhs, ast, get_reaching_val) {
            fold_expr_id(
               *rhs,
               ast,
               procedures,
               user_defined_types,
               global_exprs,
               interner,
               target,
            );
         }
      }
      CfgInstruction::Expression(expr) | CfgInstruction::Return(expr) | CfgInstruction::ConditionalJump(expr, _, _) => {
         if propagate_val_expr(*expr, ast, get_reaching_val) {
            fold_expr_id(
               *expr,
               ast,
               procedures,
               user_defined_types,
               global_exprs,
               interner,
               target,
            );
         }
      }
      CfgInstruction::Nop | CfgInstruction::Jump(_) => (),
   }
}

// Conditional Copy/Constant Propagation
pub fn propagate(program: &mut Program, interner: &Interner, target: BaseTarget) {
   program.procedure_bodies.par_values_mut().for_each(|proc| {
      let mut escaping_vars = HashSet::new();
      mark_escaping_vars_cfg(&proc.cfg, &mut escaping_vars, &proc.ast.expressions);

      let mut reaching_values: HashMap<VariableId, Option<ReachingVal>> = HashMap::new();

      'outer: loop {
         let all_reaching_defs = reaching_definitions(&proc.locals, &proc.cfg, &proc.ast.expressions);
         let rpo = &all_reaching_defs.rpo;
         let mut assignments_here = vec![None; proc.locals.len()];
         let mut assigned_variables = Vec::new();
         for (rpo_index, bb_index) in rpo.iter().enumerate() {
            for (i, instr) in proc.cfg.bbs[*bb_index].instructions.iter().enumerate() {
               reaching_values.clear();
               let get_reaching_val = |v: VariableId, ast: &ExpressionPool| -> Option<ReachingVal> {
                  // The analysis models direct assignments. Address-taken locals
                  // also participate, but alias writes make them unsafe to substitute.
                  if escaping_vars.contains(&v) {
                     return None;
                  }
                  let variable_index = proc.locals.get_index_of(&v)?;
                  let var_rd =
                     all_reaching_defs.at_statement(*bb_index, variable_index, assignments_here[variable_index]);
                  let the_reaching_val = var_rd
                     .iter()
                     .next()
                     .and_then(|x| find_reaching_val(x, &proc.cfg, rpo, ast))?;
                  if !var_rd
                     .iter()
                     .skip(1)
                     .all(|x| find_reaching_val(x, &proc.cfg, rpo, ast) == Some(the_reaching_val))
                  {
                     return None;
                  }
                  // We have ensured that there is a single reaching value, or multiple equivalent reaching values
                  // For constants, we are done. For vars, this is insufficient.
                  // 1. The var may be escaping or a global, in which case its value may have changed
                  // 2. The var may have been updated
                  if let ReachingVal::Var(reaching_var) = the_reaching_val {
                     if escaping_vars.contains(&reaching_var) {
                        return None;
                     }
                     // The reaching def of this var must not have changed between this use and the def
                     let reaching_var_index = proc.locals.get_index_of(&reaching_var)?;
                     let reaching_defs_of_reaching_var_here = all_reaching_defs.at_statement(
                        *bb_index,
                        reaching_var_index,
                        assignments_here[reaching_var_index],
                     );
                     if !var_rd.iter().all(|def_this_val_came_from| {
                        let Definition::DefinedAt(def_loc) = def_this_val_came_from else {
                           unreachable!()
                        };
                        get_reaching_defs_for_var_at_loc(
                           &all_reaching_defs,
                           def_loc,
                           reaching_var_index,
                           &proc.locals,
                           &proc.cfg,
                           ast,
                        ) == reaching_defs_of_reaching_var_here
                     }) {
                        return None;
                     }
                  }
                  Some(the_reaching_val)
               };
               let mut get_reaching_val_memoized = |v: VariableId, ast: &ExpressionPool| -> Option<ReachingVal> {
                  *reaching_values.entry(v).or_insert_with(|| get_reaching_val(v, ast))
               };

               propagate_vals(
                  instr,
                  &mut proc.ast.expressions,
                  &mut get_reaching_val_memoized,
                  &program.procedures,
                  &program.user_defined_types,
                  &program.global_exprs,
                  interner,
                  target,
               );

               if let CfgInstruction::Assignment(lhs, _) = instr
                  && let Expression::Variable(v) = proc.ast.expressions[*lhs].expression
                  && let Some(variable_index) = proc.locals.get_index_of(&v)
                  && assignments_here[variable_index]
                     .replace(ProgramIndex(rpo_index, i))
                     .is_none()
                  {
                     assigned_variables.push(variable_index);
                  }
            }

            for variable_index in assigned_variables.drain(..) {
               assignments_here[variable_index] = None;
            }

            // If we are conditionally jumping, try to prune it now that we have propagated constants.
            // This may prune reaching definitions, making our optimization more precise.
            let (jump_target, dead_target) =
               if let Some(CfgInstruction::ConditionalJump(cond, then_target, else_target)) =
                  proc.cfg.bbs[*bb_index].instructions.last()
               {
                  match proc.ast.expressions[*cond].expression {
                     Expression::BoolLiteral(true) => (*then_target, *else_target),
                     Expression::BoolLiteral(false) => (*else_target, *then_target),
                     _ => continue,
                  }
               } else {
                  continue;
               };
            *proc.cfg.bbs[*bb_index].instructions.last_mut().unwrap() = CfgInstruction::Jump(jump_target);
            proc.cfg.remove_pred_and_prune_unreachable(dead_target, *bb_index);

            // We currently recompute reaching definitions across the whole CFG.
            // This is correct but this seems like overkill -
            // there should be some way to populate an initial worklist that contains only CFGs impacted by
            // the pruning
            // (although actually that might be difficult because we may have invalidated program indices? damn.)
            continue 'outer;
         }
         break;
      }
   });
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
enum Definition {
   NoDefinitionInProc,
   DefinedAt(ProgramIndex),
}

#[derive(Clone)]
struct ReachingDefsState {
   r_in: BitBox,
   r_out: BitBox,
   gen_: BitBox,
   kill: BitBox,
}

#[derive(Clone, Default)]
struct SparseReachingDefsState {
   r_in: Vec<usize>,
   r_out: Vec<usize>,
}

enum ReachingDefsStorage {
   Dense(Vec<ReachingDefsState>),
   Sparse(Vec<SparseReachingDefsState>),
}

struct ReachingDefs {
   state: ReachingDefsStorage,
   // Indexed exactly like procedure locals, including address-taken variables.
   // Each local's definitions occupy one contiguous range of IDs.
   definition_ranges: Vec<Range<usize>>,
   definitions: Vec<Definition>,
   rpo: Vec<usize>,
}

impl ReachingDefs {
   fn at_statement(
      &self,
      block: usize,
      variable_index: usize,
      assignment: Option<ProgramIndex>,
   ) -> VariableDefinitions<'_> {
      if let Some(loc) = assignment {
         VariableDefinitions::Assigned(loc)
      } else {
         self.at_block_entry(block, &self.definition_ranges[variable_index])
      }
   }

   fn at_block_entry(&self, block: usize, range: &Range<usize>) -> VariableDefinitions<'_> {
      match &self.state {
         ReachingDefsStorage::Dense(state) => VariableDefinitions::BlockEntry {
            bits: &state[block].r_in[range.clone()],
            definitions: &self.definitions[range.clone()],
         },
         ReachingDefsStorage::Sparse(state) => {
            let input = &state[block].r_in;
            let start = input.partition_point(|id| *id < range.start);
            let end = input.partition_point(|id| *id < range.end);
            VariableDefinitions::SparseEntry {
               indices: &input[start..end],
               definitions: &self.definitions,
            }
         }
      }
   }
}

#[derive(Clone, Copy)]
enum VariableDefinitions<'a> {
   BlockEntry {
      bits: &'a BitSlice,
      definitions: &'a [Definition],
   },
   SparseEntry {
      indices: &'a [usize],
      definitions: &'a [Definition],
   },
   Assigned(ProgramIndex),
}

impl VariableDefinitions<'_> {
   fn iter(&self) -> impl Iterator<Item = Definition> {
      let (single, bits, indices, definitions) = match *self {
         Self::BlockEntry { bits, definitions } => (None, bits, &[][..], definitions),
         Self::SparseEntry { indices, definitions } => (None, BitSlice::empty(), indices, definitions),
         Self::Assigned(loc) => (Some(Definition::DefinedAt(loc)), BitSlice::empty(), &[][..], &[][..]),
      };
      single.into_iter().chain(
         bits
            .iter_ones()
            .chain(indices.iter().copied())
            .map(move |i| definitions[i]),
      )
   }
}

impl PartialEq for VariableDefinitions<'_> {
   fn eq(&self, other: &Self) -> bool {
      // Bit indices within each variable's range have a canonical definition order.
      self.iter().eq(other.iter())
   }
}

fn get_reaching_defs_for_var_at_loc<'r>(
   reaching_defs: &'r ReachingDefs,
   loc: ProgramIndex,
   variable_index: usize,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &Cfg,
   ast: &ExpressionPool,
) -> VariableDefinitions<'r> {
   let (var, _) = procedure_vars.get_index(variable_index).unwrap();
   let bb_index = reaching_defs.rpo[loc.0];
   for (i, instr) in cfg.bbs[bb_index].instructions[..loc.1].iter().enumerate().rev() {
      if let CfgInstruction::Assignment(lhs, _) = instr
         && let Expression::Variable(v) = ast[*lhs].expression
         && v == *var
      {
         return VariableDefinitions::Assigned(ProgramIndex(loc.0, i));
      }
   }

   reaching_defs.at_block_entry(bb_index, &reaching_defs.definition_ranges[variable_index])
}

#[must_use]
fn reaching_definitions(
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &Cfg,
   ast: &ExpressionPool,
) -> ReachingDefs {
   let mut definition_ranges = vec![0..1; procedure_vars.len()];
   let rpo: Vec<_> = post_order(cfg).into_iter().rev().collect();

   let mut block_definitions = vec![Vec::new(); cfg.bbs.len()];
   let mut last_definition = vec![None; procedure_vars.len()];
   let mut generated_variables = Vec::new();
   for (rpo_index, bb) in rpo.iter().copied().enumerate() {
      for (i, instruction) in cfg.bbs[bb].instructions.iter().enumerate() {
         if let CfgInstruction::Assignment(lhs, _) = instruction
            && let Expression::Variable(v) = ast[*lhs].expression
            && let Some(variable_index) = procedure_vars.get_index_of(&v)
            && last_definition[variable_index]
               .replace(ProgramIndex(rpo_index, i))
               .is_none()
            {
               generated_variables.push(variable_index);
            }
      }
      for variable_index in generated_variables.drain(..) {
         definition_ranges[variable_index].end += 1;
         block_definitions[bb].push((variable_index, last_definition[variable_index].take().unwrap()));
      }
   }
   let mut num_definitions = 0;
   for range in definition_ranges.iter_mut() {
      let count = range.end;
      *range = num_definitions..num_definitions + count;
      num_definitions += count;
   }
   let mut definitions = vec![Definition::NoDefinitionInProc; num_definitions];
   let mut next_definition: Vec<_> = definition_ranges.iter().map(|range| range.start + 1).collect();
   let mut gen_: Vec<Vec<(usize, usize)>> = vec![Vec::new(); cfg.bbs.len()];
   for bb_index in rpo.iter().copied() {
      for (variable_index, loc) in block_definitions[bb_index].drain(..) {
         let definition_index = next_definition[variable_index];
         next_definition[variable_index] += 1;
         definitions[definition_index] = Definition::DefinedAt(loc);
         gen_[bb_index].push((variable_index, definition_index));
      }
   }
   // Uninitialized and input variables need a pseudo definition so that
   // if the var is used and then assigned in a loop we don't propagate
   // the value backwards
   let mut defined_at_start = bitvec![0; procedure_vars.len()];
   for (variable_index, _) in gen_[cfg.start].iter() {
      defined_at_start.set(*variable_index, true);
   }
   for (variable_index, range) in definition_ranges.iter().enumerate() {
      if !defined_at_start[variable_index] {
         gen_[cfg.start].push((variable_index, range.start));
      }
   }
   for block_gen in gen_.iter_mut() {
      block_gen.sort_unstable();
   }

   let state = {
      // A word-sized bitset costs about as much to visit as one sparse definition.
      // Try sparse storage when the bitset is wider than the initial reaching set;
      // abandon it if unions grow beyond that size (for example, around a loop).
      let words = num_definitions.div_ceil(usize::BITS as usize);
      let sparse = if words > procedure_vars.len() {
         try_solve_sparse(cfg, &rpo, &definition_ranges, &gen_, words)
      } else {
         None
      };
      if let Some(sparse) = sparse {
         ReachingDefsStorage::Sparse(sparse)
      } else {
         ReachingDefsStorage::Dense(solve_dense(cfg, &rpo, &definition_ranges, &gen_, num_definitions))
      }
   };

   ReachingDefs {
      state,
      definition_ranges,
      definitions,
      rpo,
   }
}

fn solve_dense(
   cfg: &Cfg,
   rpo: &[usize],
   definition_ranges: &[Range<usize>],
   gen_: &[Vec<(usize, usize)>],
   num_definitions: usize,
) -> Vec<ReachingDefsState> {
   let mut state = vec![
      ReachingDefsState {
         r_in: bitbox![0; num_definitions],
         r_out: bitbox![0; num_definitions],
         gen_: bitbox![0; num_definitions],
         kill: bitbox![0; num_definitions],
      };
      cfg.bbs.len()
   ];
   for (bb_index, block_gen) in gen_.iter().enumerate() {
      for (variable_index, definition_index) in block_gen {
         let range = &definition_ranges[*variable_index];
         state[bb_index].kill[range.clone()].fill(true);
         state[bb_index].gen_.set(*definition_index, true);
      }
   }
   // Forwards analysis, which is RPO - the R comes from popping off the worlist
   let mut worklist: IndexSet<usize> = rpo.iter().rev().copied().collect();
   while let Some(node_id) = worklist.pop() {
      // Update in
      {
         let mut new_r_in = std::mem::replace(&mut state[node_id].r_in, bitbox![0; 0]);
         // Reaching sets only grow within one solve, so the predecessor union can
         // accumulate in place. A CFG change starts a fresh solve.
         for predecessor in cfg.bbs[node_id].predecessors.iter().copied() {
            new_r_in |= &state[predecessor].r_out;
         }
         state[node_id].r_in = new_r_in;
      }

      // Update out
      {
         let s = &mut state[node_id];
         let mut difference = 0;
         for (((input, kill), gen_), output) in s
            .r_in
            .as_raw_slice()
            .iter()
            .zip(s.kill.as_raw_slice())
            .zip(s.gen_.as_raw_slice())
            .zip(s.r_out.as_raw_mut_slice())
         {
            let next = gen_ | (input & !kill);
            difference |= next ^ *output;
            *output = next;
         }
         if difference != 0 {
            worklist.extend(&cfg.bbs[node_id].successors());
         }
      }
   }

   state
}

fn try_solve_sparse(
   cfg: &Cfg,
   rpo: &[usize],
   definition_ranges: &[Range<usize>],
   gen_: &[Vec<(usize, usize)>],
   max_definitions: usize,
) -> Option<Vec<SparseReachingDefsState>> {
   let mut definition_variables = Vec::new();
   for (variable_index, range) in definition_ranges.iter().enumerate() {
      definition_variables.resize(range.end, variable_index);
   }
   let mut state = vec![SparseReachingDefsState::default(); cfg.bbs.len()];
   let mut worklist: IndexSet<usize> = rpo.iter().rev().copied().collect();
   let mut scratch = Vec::new();
   while let Some(node_id) = worklist.pop() {
      let mut input = std::mem::take(&mut state[node_id].r_in);
      input.clear();
      for predecessor in cfg.bbs[node_id].predecessors.iter().copied() {
         union_sorted_definitions(&mut input, &state[predecessor].r_out, &mut scratch);
         if input.len() > max_definitions {
            return None;
         }
      }
      let block_gen = &gen_[node_id];
      scratch.clear();
      scratch.extend(input.iter().copied().filter(|id| {
         block_gen
            .binary_search_by_key(&definition_variables[*id], |(variable_index, _)| *variable_index)
            .is_err()
      }));
      scratch.extend(block_gen.iter().map(|(_, definition_index)| *definition_index));
      if scratch.len() > max_definitions {
         return None;
      }
      // Killed variables were removed, so generated definitions cannot be duplicates.
      scratch.sort_unstable();
      state[node_id].r_in = input;
      if scratch != state[node_id].r_out {
         std::mem::swap(&mut scratch, &mut state[node_id].r_out);
         worklist.extend(cfg.bbs[node_id].successors());
      }
   }
   Some(state)
}

fn union_sorted_definitions(left: &mut Vec<usize>, right: &[usize], scratch: &mut Vec<usize>) {
   scratch.clear();
   let (mut l, mut r) = (0, 0);
   while l < left.len() && r < right.len() {
      match left[l].cmp(&right[r]) {
         std::cmp::Ordering::Less => {
            scratch.push(left[l]);
            l += 1;
         }
         std::cmp::Ordering::Greater => {
            scratch.push(right[r]);
            r += 1;
         }
         std::cmp::Ordering::Equal => {
            scratch.push(left[l]);
            l += 1;
            r += 1;
         }
      }
   }
   scratch.extend_from_slice(&left[l..]);
   scratch.extend_from_slice(&right[r..]);
   std::mem::swap(left, scratch);
}

// MARK: Escape Analysis

fn mark_escaping_vars_cfg(cfg: &Cfg, escaping_vars: &mut HashSet<VariableId>, ast: &ExpressionPool) {
   for bb in post_order(cfg) {
      for instr in cfg.bbs[bb].instructions.iter() {
         match instr {
            CfgInstruction::Assignment(lhs, rhs) => {
               if !matches!(ast[*lhs].expression, Expression::Variable(_)) {
                  mark_escaping_vars_expr(*lhs, escaping_vars, ast);
               }
               mark_escaping_vars_expr(*rhs, escaping_vars, ast);
            }
            CfgInstruction::Expression(e) | CfgInstruction::ConditionalJump(e, _, _) | CfgInstruction::Return(e) => {
               mark_escaping_vars_expr(*e, escaping_vars, ast);
            }
            _ => (),
         }
      }
   }
}

fn mark_escaping_vars_expr(in_expr: ExpressionId, escaping_vars: &mut HashSet<VariableId>, ast: &ExpressionPool) {
   match &ast[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_escaping_vars_expr(*proc_expr, escaping_vars, ast);

         for val in args.iter().map(|x| x.expr) {
            mark_escaping_vars_expr(val, escaping_vars, ast);
         }
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         mark_escaping_vars_expr(*lhs, escaping_vars, ast);
         mark_escaping_vars_expr(*rhs, escaping_vars, ast);
      }
      Expression::IfX(a, b, c) => {
         mark_escaping_vars_expr(*a, escaping_vars, ast);
         mark_escaping_vars_expr(*b, escaping_vars, ast);
         mark_escaping_vars_expr(*c, escaping_vars, ast);
      }
      Expression::Cast { expr, .. } => {
         mark_escaping_vars_expr(*expr, escaping_vars, ast);
      }
      Expression::UnaryOperator(op, expr) => {
         let is_variable_load = *op == UnOp::Dereference && matches!(ast[*expr].expression, Expression::Variable(_));
         if !is_variable_load {
            mark_escaping_vars_expr(*expr, escaping_vars, ast);
         }
      }
      Expression::Variable(v) => {
         escaping_vars.insert(*v);
      }
      Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => (),
      Expression::ArrayIndex { .. }
      | Expression::FieldAccess(_, _)
      | Expression::StructLiteral(_, _)
      | Expression::ArrayLiteral(_)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}
