use std::collections::{HashMap, HashSet};
use std::iter;

use indexmap::{IndexMap, IndexSet};
use slotmap::SlotMap;

use crate::backend::linearize::{post_order, Cfg, CfgInstruction, CFG_START_NODE};
use crate::backend::liveness::ProgramIndex;
use crate::constant_folding::{self, is_non_aggregate_const, FoldingContext};
use crate::expression_hoisting::is_reinterpretable_transmute;
use crate::interner::Interner;
use crate::parse::{
   AstPool, CastType, Expression, ExpressionId, ExpressionPool, ProcedureId, ProcedureNode, UnOp, UserDefinedTypeInfo,
   VariableId,
};
use crate::type_data::ExpressionType;
use crate::{Program, Target};

fn fold_expr_id(
   expr_id: ExpressionId,
   ast: &mut AstPool,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
   interner: &Interner,
   target: Target,
) {
   let mut fc = FoldingContext {
      ast,
      procedures,
      user_defined_types,
      const_replacements: &HashMap::new(),
      current_proc_name: None,
      target,
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
         } else if let Expression::Variable(v) = e {
            Some(ReachingVal::Var(*v))
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
   reaching_values: &HashMap<VariableId, ReachingVal>,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
   interner: &Interner,
   target: Target,
) {
   fn propagate_val_expr(
      e: ExpressionId,
      ast: &mut ExpressionPool,
      reaching_values: &HashMap<VariableId, ReachingVal>,
      is_lhs_context: bool,
   ) -> bool {
      let mut propagated_const = false;
      let mut the_expression = std::mem::replace(&mut ast[e].expression, Expression::UnitLiteral);
      match &the_expression {
         Expression::Variable(v) => {
            if !is_lhs_context {
               match reaching_values.get(v) {
                  Some(ReachingVal::Const(c)) => {
                     the_expression = ast[*c].expression.clone();
                     propagated_const = true;
                  }
                  Some(ReachingVal::Var(v)) => {
                     the_expression = Expression::Variable(*v);
                  }
                  None => (),
               }
            }
         }
         Expression::UnaryOperator(UnOp::AddressOf, child) => {
            propagated_const |= propagate_val_expr(*child, ast, reaching_values, true);
         }
         Expression::UnaryOperator(UnOp::Dereference, child) => {
            propagated_const |= propagate_val_expr(*child, ast, reaching_values, false);
         }
         Expression::Cast {
            cast_type: CastType::Transmute,
            target_type,
            expr: child,
         } => {
            propagated_const |= propagate_val_expr(
               *child,
               ast,
               reaching_values,
               !is_reinterpretable_transmute(ast[*child].exp_type.as_ref().unwrap(), target_type),
            );
         }
         Expression::UnaryOperator(_, child) | Expression::Cast { expr: child, .. } => {
            propagated_const |= propagate_val_expr(*child, ast, reaching_values, is_lhs_context);
         }
         Expression::ArrayIndex { array, index } => {
            propagated_const |= propagate_val_expr(*array, ast, reaching_values, true);
            propagated_const |= propagate_val_expr(*index, ast, reaching_values, false);
         }
         Expression::ProcedureCall { proc_expr, args } => {
            propagated_const |= propagate_val_expr(*proc_expr, ast, reaching_values, is_lhs_context);
            for arg in args.iter() {
               propagated_const |= propagate_val_expr(arg.expr, ast, reaching_values, is_lhs_context);
            }
         }
         Expression::BinaryOperator { lhs, rhs, .. } => {
            propagated_const |= propagate_val_expr(*lhs, ast, reaching_values, true);
            propagated_const |= propagate_val_expr(*rhs, ast, reaching_values, false);
         }
         Expression::FieldAccess(_, base) => {
            propagated_const |= propagate_val_expr(*base, ast, reaching_values, true);
         }
         Expression::IfX(a, b, c) => {
            propagated_const |= propagate_val_expr(*a, ast, reaching_values, is_lhs_context);
            propagated_const |= propagate_val_expr(*b, ast, reaching_values, is_lhs_context);
            propagated_const |= propagate_val_expr(*c, ast, reaching_values, is_lhs_context);
         }
         Expression::BoolLiteral(_)
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
         if propagate_val_expr(*lhs, &mut ast.expressions, reaching_values, true) {
            fold_expr_id(*lhs, ast, procedures, user_defined_types, interner, target);
         }
         if propagate_val_expr(*rhs, &mut ast.expressions, reaching_values, false) {
            fold_expr_id(*rhs, ast, procedures, user_defined_types, interner, target);
         }
      }
      CfgInstruction::Expression(expr)
      | CfgInstruction::Return(expr)
      | CfgInstruction::IfElse(expr, _, _, _)
      | CfgInstruction::ConditionalJump(expr, _, _) => {
         if propagate_val_expr(*expr, &mut ast.expressions, reaching_values, false) {
            fold_expr_id(*expr, ast, procedures, user_defined_types, interner, target);
         }
      }
      CfgInstruction::Break
      | CfgInstruction::Continue
      | CfgInstruction::Nop
      | CfgInstruction::Jump(_)
      | CfgInstruction::Loop(_, _) => (),
   }
}

pub fn prune_dead_branches(program: &mut Program) {
   for proc in program.procedure_bodies.values_mut() {
      for i in post_order(&proc.cfg).iter().rev() {
         let bb = &mut proc.cfg.bbs[*i];
         let (jump_target, dead_target) =
            if let Some(CfgInstruction::ConditionalJump(cond, then_target, else_target)) = bb.instructions.last_mut() {
               match program.ast.expressions[*cond].expression {
                  Expression::BoolLiteral(true) => (*then_target, *else_target),
                  Expression::BoolLiteral(false) => (*else_target, *then_target),
                  _ => continue,
               }
            } else {
               continue;
            };
         *bb.instructions.last_mut().unwrap() = CfgInstruction::Jump(jump_target);
         proc.cfg.bbs[dead_target].predecessors.remove(i);
      }
   }
}

pub fn propagate_constants(program: &mut Program, interner: &Interner, target: Target) {
   for proc in program.procedure_bodies.values() {
      let mut escaping_vars = HashSet::new();
      mark_escaping_vars_cfg(&proc.cfg, &mut escaping_vars, &program.ast.expressions);
      let reaching_defs = reaching_definitions(&proc.locals, &proc.cfg, &program.ast.expressions);

      let mut reaching_values: HashMap<VariableId, ReachingVal> = HashMap::new();
      let rpo = {
         let mut x = post_order(&proc.cfg);
         x.reverse();
         x
      };
      for (rpo_index, bb_index) in rpo.iter().enumerate() {
         for (i, instr) in proc.cfg.bbs[*bb_index].instructions.iter().enumerate() {
            // Compute the reaching values
            {
               let rds = &reaching_defs[&ProgramIndex(rpo_index, i)].def;
               let reaching_partial_defs = &reaching_defs[&ProgramIndex(rpo_index, i)].partials;
               reaching_values.clear();
               for (var, var_rd) in rds.iter() {
                  if escaping_vars.contains(var) {
                     continue;
                  }
                  if !reaching_partial_defs.get(var).map_or(true, HashSet::is_empty) {
                     continue;
                  }
                  let Some(the_reaching_val) = var_rd
                     .iter()
                     .next()
                     .and_then(|x| find_reaching_val(*x, &proc.cfg, &rpo, &program.ast.expressions))
                  else {
                     continue;
                  };
                  if !var_rd.iter().skip(1).all(|x| {
                     find_reaching_val(*x, &proc.cfg, &rpo, &program.ast.expressions) == Some(the_reaching_val)
                  }) {
                     continue;
                  }
                  // We have ensured that there is a single reaching value, or multiple equivalent reaching values
                  // For constants, we are done. For vars, this is insufficient.
                  // 1. The var may be escaping or a global, in which case its value may have changed
                  // 2. The var may have been updated either partially or fully
                  if let ReachingVal::Var(v) = the_reaching_val {
                     if escaping_vars.contains(&v) {
                        continue;
                     }
                     if !proc.locals.contains_key(&v) {
                        continue;
                     }
                     // The reaching def of this var must not have changed between this use and the def
                     let empty_definitions = HashSet::new();
                     let reaching_defs_of_v_here = &rds.get(&v).unwrap_or(&empty_definitions);
                     let partial_reaching_defs_of_v_here = &reaching_partial_defs.get(&v).unwrap_or(&empty_definitions);
                     if !var_rd.iter().all(|def_this_val_came_from| {
                        let Definition::DefinedAt(loc) = def_this_val_came_from else {
                           unreachable!()
                        };
                        reaching_defs[loc].def.get(&v).unwrap_or(&empty_definitions) == *reaching_defs_of_v_here
                           && reaching_defs[loc].partials.get(&v).unwrap_or(&empty_definitions)
                              == *partial_reaching_defs_of_v_here
                     }) {
                        continue;
                     }
                  }
                  reaching_values.insert(*var, the_reaching_val);
               }
            }

            propagate_vals(
               instr,
               &mut program.ast,
               &reaching_values,
               &program.procedures,
               &program.user_defined_types,
               interner,
               target,
            );
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
type PartialDefMap = HashMap<VariableId, HashSet<Definition>>;

#[derive(Clone, Default, PartialEq)]
struct MultiDefsAndPartials {
   def: MultiDefMap,
   partials: PartialDefMap,
}

impl MultiDefsAndPartials {
   fn new() -> MultiDefsAndPartials {
      MultiDefsAndPartials {
         def: MultiDefMap::new(),
         partials: PartialDefMap::new(),
      }
   }

   fn clear(&mut self) {
      self.def.clear();
      self.partials.clear();
   }
}

#[derive(Clone, Default, PartialEq)]

struct SingleDefAndPartials {
   def: DefinitionMap,
   partials: PartialDefMap,
}

impl SingleDefAndPartials {
   fn new() -> SingleDefAndPartials {
      SingleDefAndPartials {
         def: DefinitionMap::new(),
         partials: PartialDefMap::new(),
      }
   }
}

#[derive(Clone)]
struct ReachingDefsState {
   r_in: MultiDefsAndPartials,
   r_out: MultiDefsAndPartials,
   gen: SingleDefAndPartials,
   // kill is implicit from gen
}

#[must_use]
fn reaching_definitions(
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &Cfg,
   ast: &ExpressionPool,
) -> IndexMap<ProgramIndex, MultiDefsAndPartials> {
   // Dataflow Analyis on the CFG
   let mut state = vec![
      ReachingDefsState {
         r_in: MultiDefsAndPartials::new(),
         r_out: MultiDefsAndPartials::new(),
         gen: SingleDefAndPartials::new(),
      };
      cfg.bbs.len()
   ];

   // Setup
   for (i, bb_index) in post_order(cfg).iter().rev().enumerate() {
      // The last definition is the one we care about; so go back to front
      for (j, instruction) in cfg.bbs[*bb_index].instructions.iter().enumerate().rev() {
         if let CfgInstruction::Assignment(lhs, _) = instruction {
            if let Expression::Variable(v) = ast[*lhs].expression {
               if procedure_vars.contains_key(&v) {
                  state[*bb_index]
                     .gen
                     .def
                     .entry(v)
                     .or_insert(Definition::DefinedAt(ProgramIndex(i, j)));
               }
            } else if let Some(v) = partially_accessed_var(*lhs, ast) {
               if procedure_vars.contains_key(&v) && !state[*bb_index].gen.def.contains_key(&v) {
                  state[*bb_index]
                     .gen
                     .partials
                     .entry(v)
                     .or_default()
                     .insert(Definition::DefinedAt(ProgramIndex(i, j)));
               }
            }
         }
      }
   }
   // Uninitialized and input variables need a pseudo definition so that
   // if the var is used and then assigned in a loop we don't propagate
   // the value backwards
   for proc_var in procedure_vars.keys().copied() {
      state[CFG_START_NODE]
         .gen
         .def
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
            for (var, defs) in &pred_out.def {
               new_r_in.def.entry(*var).or_default().extend(defs.iter());
            }
            for (var, partial_defs) in &pred_out.partials {
               new_r_in.partials.entry(*var).or_default().extend(partial_defs.iter());
            }
         }
         state[node_id].r_in = new_r_in;
      }

      // Update out
      {
         let s = &mut state[node_id];
         let old_r_out = std::mem::replace(
            &mut s.r_out,
            MultiDefsAndPartials {
               def: s.gen.def.iter().map(|(k, v)| (*k, iter::once(*v).collect())).collect(),
               partials: s.gen.partials.clone(),
            },
         );

         for (var, defs) in s.r_in.def.iter() {
            if s.gen.def.contains_key(var) {
               continue;
            }
            s.r_out.def.entry(*var).or_default().extend(defs);
         }
         for (var, partial_defs) in s.r_in.partials.iter() {
            if s.gen.def.contains_key(var) {
               continue;
            }
            s.r_out.partials.entry(*var).or_default().extend(partial_defs);
         }

         if old_r_out != s.r_out {
            worklist.extend(&cfg.bbs[node_id].successors());
         }
      }
   }

   // Construct the final results
   let mut all_reaching_defs: IndexMap<ProgramIndex, MultiDefsAndPartials> = IndexMap::new();
   let mut current_reaching_defs = MultiDefsAndPartials::new();
   for (rpo_index, node_id) in post_order(cfg).iter().copied().rev().enumerate() {
      let bb = &cfg.bbs[node_id];
      let s = &state[node_id];
      current_reaching_defs.clear();
      current_reaching_defs
         .def
         .extend(s.r_in.def.iter().map(|(k, v)| (*k, v.clone())));
      all_reaching_defs.reserve(bb.instructions.len());
      for (i, instruction) in bb.instructions.iter().enumerate() {
         let pi = ProgramIndex(rpo_index, i);
         all_reaching_defs.insert(pi, current_reaching_defs.clone());
         if let CfgInstruction::Assignment(lhs, _) = instruction {
            if let Expression::Variable(v) = ast[*lhs].expression {
               if procedure_vars.contains_key(&v) {
                  let reaching_defs = current_reaching_defs.def.entry(v).or_default();
                  reaching_defs.clear();
                  reaching_defs.insert(Definition::DefinedAt(ProgramIndex(rpo_index, i)));
                  current_reaching_defs.partials.entry(v).or_default().clear();
               }
            } else if let Some(v) = partially_accessed_var(*lhs, ast) {
               if procedure_vars.contains_key(&v) {
                  current_reaching_defs
                     .partials
                     .entry(v)
                     .or_default()
                     .insert(Definition::DefinedAt(ProgramIndex(rpo_index, i)));
               }
            }
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
               mark_escaping_vars_expr(*lhs, escaping_vars, ast);
               mark_escaping_vars_expr(*rhs, escaping_vars, ast);
            }
            CfgInstruction::Expression(e)
            | CfgInstruction::ConditionalJump(e, _, _)
            | CfgInstruction::Return(e)
            | CfgInstruction::IfElse(e, _, _, _) => {
               mark_escaping_vars_expr(*e, escaping_vars, ast);
            }
            _ => (),
         }
      }
   }
}

pub fn partially_accessed_var(e: ExpressionId, ast: &ExpressionPool) -> Option<VariableId> {
   match &ast[e].expression {
      Expression::ArrayIndex { array, .. } => partially_accessed_var(*array, ast),
      Expression::FieldAccess(_, base) => partially_accessed_var(*base, ast),
      Expression::Variable(v) => Some(*v),
      _ => None,
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
      Expression::ArrayIndex { array, index } => {
         mark_escaping_vars_expr(*array, escaping_vars, ast);
         mark_escaping_vars_expr(*index, escaping_vars, ast);
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
      Expression::FieldAccess(_, base_expr) => {
         mark_escaping_vars_expr(*base_expr, escaping_vars, ast);
      }
      Expression::Cast { expr, .. } => {
         mark_escaping_vars_expr(*expr, escaping_vars, ast);
      }
      Expression::UnaryOperator(op, expr) => {
         mark_escaping_vars_expr(*expr, escaping_vars, ast);
         if *op == UnOp::AddressOf {
            if let Some(v) = partially_accessed_var(*expr, ast) {
               escaping_vars.insert(v);
            }
         }
      }
      Expression::Variable(_)
      | Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => (),
      Expression::StructLiteral(_, _)
      | Expression::ArrayLiteral(_)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}
