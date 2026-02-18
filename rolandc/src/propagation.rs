use std::collections::{HashMap, HashSet};
use std::iter;

use indexmap::{IndexMap, IndexSet};
use slotmap::SlotMap;

use crate::backend::linearize::{Cfg, CfgInstruction, post_order};
use crate::backend::liveness::ProgramIndex;
use crate::constant_folding::{self, FoldingContext, is_non_aggregate_const};
use crate::interner::Interner;
use crate::parse::{
   AstPool, Expression, ExpressionId, ExpressionPool, ProcedureId, ProcedureNode, UnOp, UserDefinedTypeInfo, VariableId,
};
use crate::type_data::ExpressionType;
use crate::{BaseTarget, Program};

fn fold_expr_id(
   expr_id: ExpressionId,
   ast: &mut AstPool,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
   interner: &Interner,
   target: BaseTarget,
) {
   let mut fc = FoldingContext {
      ast,
      procedures,
      user_defined_types,
      const_replacements: &HashMap::new(),
      current_proc_name: None,
      target,
      templated_types: &HashMap::new(),
   };
   constant_folding::try_fold_and_replace_expr(expr_id, &mut None, &mut fc, interner);
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
   ast: &mut AstPool,
   get_reaching_val: &mut impl FnMut(VariableId, &ExpressionPool) -> Option<ReachingVal>,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
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
         if propagate_val_expr(*lhs, &mut ast.expressions, get_reaching_val) {
            fold_expr_id(*lhs, ast, procedures, user_defined_types, interner, target);
         }
         if propagate_val_expr(*rhs, &mut ast.expressions, get_reaching_val) {
            fold_expr_id(*rhs, ast, procedures, user_defined_types, interner, target);
         }
      }
      CfgInstruction::Expression(expr) | CfgInstruction::Return(expr) | CfgInstruction::ConditionalJump(expr, _, _) => {
         if propagate_val_expr(*expr, &mut ast.expressions, get_reaching_val) {
            fold_expr_id(*expr, ast, procedures, user_defined_types, interner, target);
         }
      }
      CfgInstruction::Nop | CfgInstruction::Jump(_) => (),
   }
}

// Conditional Copy/Constant Propagation
pub fn propagate(program: &mut Program, interner: &Interner, target: BaseTarget) {
   let empty_definitions = HashSet::new();
   for proc in program.procedure_bodies.values_mut() {
      let mut escaping_vars = HashSet::new();
      mark_escaping_vars_cfg(&proc.cfg, &mut escaping_vars, &program.ast.expressions);
      let mut all_reaching_defs = reaching_definitions(&proc.locals, &proc.cfg, &program.ast.expressions);

      let mut reaching_values: HashMap<VariableId, Option<ReachingVal>> = HashMap::new();
      let rpo = {
         let mut x = post_order(&proc.cfg);
         x.reverse();
         x
      };
      let mut reachable_bbs: HashSet<usize> = rpo.iter().copied().collect();
      for (rpo_index, bb_index) in rpo.iter().enumerate() {
         for (i, instr) in proc.cfg.bbs[*bb_index].instructions.iter().enumerate() {
            let reaching_defs = &all_reaching_defs[&ProgramIndex(rpo_index, i)];

            reaching_values.clear();
            let get_reaching_val = |v: VariableId, ast: &ExpressionPool| -> Option<ReachingVal> {
               if escaping_vars.contains(&v) {
                  return None;
               }
               let var_rd = reaching_defs.get(&v)?;
               let the_reaching_val = var_rd
                  .iter()
                  .next()
                  .and_then(|x| find_reaching_val(*x, &proc.cfg, &rpo, ast))?;
               if !var_rd
                  .iter()
                  .skip(1)
                  .all(|x| find_reaching_val(*x, &proc.cfg, &rpo, ast) == Some(the_reaching_val))
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
                  if !proc.locals.contains_key(&reaching_var) {
                     return None;
                  }
                  // The reaching def of this var must not have changed between this use and the def
                  let reaching_defs_of_v_here = &reaching_defs.get(&reaching_var).unwrap_or(&empty_definitions);
                  if !var_rd.iter().all(|def_this_val_came_from| {
                     let Definition::DefinedAt(loc) = def_this_val_came_from else {
                        unreachable!()
                     };
                     all_reaching_defs[loc].get(&reaching_var).unwrap_or(&empty_definitions) == *reaching_defs_of_v_here
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
               &mut program.ast,
               &mut get_reaching_val_memoized,
               &program.procedures,
               &program.user_defined_types,
               interner,
               target,
            );
         }

         // If we are conditionally jumping, try to prune it now that we have propagated constants.
         // This may prune reaching definitions, making our optimization more precise.
         let (jump_target, dead_target) = if let Some(CfgInstruction::ConditionalJump(cond, then_target, else_target)) =
            proc.cfg.bbs[*bb_index].instructions.last()
         {
            match program.ast.expressions[*cond].expression {
               Expression::BoolLiteral(true) => (*then_target, *else_target),
               Expression::BoolLiteral(false) => (*else_target, *then_target),
               _ => continue,
            }
         } else {
            continue;
         };
         *proc.cfg.bbs[*bb_index].instructions.last_mut().unwrap() = CfgInstruction::Jump(jump_target);
         proc.cfg.bbs[dead_target].predecessors.remove(bb_index);
         reachable_bbs.clear();
         reachable_bbs.extend(post_order(&proc.cfg).iter().copied());

         // Update reaching definitions
         for defs_at_given_location in all_reaching_defs.values_mut() {
            for defs in defs_at_given_location.values_mut() {
               defs.retain(|x| match x {
                  Definition::DefinedAt(loc) => reachable_bbs.contains(&rpo[loc.0]),
                  Definition::NoDefinitionInProc => true,
               });
            }
         }
      }
   }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
enum Definition {
   NoDefinitionInProc,
   DefinedAt(ProgramIndex),
}

type DefinitionMap = HashMap<VariableId, Definition>;
type MultiDefMap = HashMap<VariableId, HashSet<Definition>>;

#[derive(Clone)]
struct ReachingDefsState {
   r_in: MultiDefMap,
   r_out: MultiDefMap,
   gen_: DefinitionMap,
   // kill is implicit from gen
}

#[must_use]
fn reaching_definitions(
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &Cfg,
   ast: &ExpressionPool,
) -> IndexMap<ProgramIndex, MultiDefMap> {
   // Dataflow Analyis on the CFG
   let mut state = vec![
      ReachingDefsState {
         r_in: MultiDefMap::new(),
         r_out: MultiDefMap::new(),
         gen_: DefinitionMap::new(),
      };
      cfg.bbs.len()
   ];

   // Setup
   for (i, bb_index) in post_order(cfg).iter().rev().enumerate() {
      // The last definition is the one we care about; so go back to front
      for (j, instruction) in cfg.bbs[*bb_index].instructions.iter().enumerate().rev() {
         if let CfgInstruction::Assignment(lhs, _) = instruction
            && let Expression::Variable(v) = ast[*lhs].expression
            && procedure_vars.contains_key(&v)
         {
            state[*bb_index]
               .gen_
               .entry(v)
               .or_insert(Definition::DefinedAt(ProgramIndex(i, j)));
         }
      }
   }
   // Uninitialized and input variables need a pseudo definition so that
   // if the var is used and then assigned in a loop we don't propagate
   // the value backwards
   for proc_var in procedure_vars.keys().copied() {
      state[cfg.start]
         .gen_
         .entry(proc_var)
         .or_insert(Definition::NoDefinitionInProc);
   }
   // Forwards analysis, which is RPO - the R comes from popping off the worlist
   let mut worklist: IndexSet<usize> = post_order(cfg).into_iter().collect();
   while let Some(node_id) = worklist.pop() {
      // Update in
      {
         let mut new_r_in = std::mem::take(&mut state[node_id].r_in);
         new_r_in.clear();
         for predecessor in cfg.bbs[node_id].predecessors.iter().copied() {
            let pred_out = &state[predecessor].r_out;
            for (var, defs) in pred_out {
               new_r_in.entry(*var).or_default().extend(defs.iter());
            }
         }
         state[node_id].r_in = new_r_in;
      }

      // Update out
      {
         let s = &mut state[node_id];
         let old_r_out = std::mem::replace(
            &mut s.r_out,
            s.gen_.iter().map(|(k, v)| (*k, iter::once(*v).collect())).collect(),
         );

         for (var, defs) in s.r_in.iter() {
            if s.gen_.contains_key(var) {
               continue;
            }
            s.r_out.entry(*var).or_default().extend(defs);
         }

         if old_r_out != s.r_out {
            worklist.extend(&cfg.bbs[node_id].successors());
         }
      }
   }

   // Construct the final results
   let mut all_reaching_defs: IndexMap<ProgramIndex, MultiDefMap> = IndexMap::new();
   let mut current_reaching_defs = MultiDefMap::new();
   for (rpo_index, node_id) in post_order(cfg).iter().copied().rev().enumerate() {
      let bb = &cfg.bbs[node_id];
      let s = &state[node_id];
      current_reaching_defs.clear();
      current_reaching_defs.extend(s.r_in.iter().map(|(k, v)| (*k, v.clone())));
      all_reaching_defs.reserve(bb.instructions.len());
      for (i, instruction) in bb.instructions.iter().enumerate() {
         let pi = ProgramIndex(rpo_index, i);
         all_reaching_defs.insert(pi, current_reaching_defs.clone());
         if let CfgInstruction::Assignment(lhs, _) = instruction
            && let Expression::Variable(v) = ast[*lhs].expression
            && procedure_vars.contains_key(&v)
         {
            let reaching_defs = current_reaching_defs.entry(v).or_default();
            reaching_defs.clear();
            reaching_defs.insert(Definition::DefinedAt(ProgramIndex(rpo_index, i)));
         }
      }
   }

   all_reaching_defs
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
