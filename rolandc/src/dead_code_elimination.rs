use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use crate::backend::linearize::{post_order, CfgInstruction};
use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionPool, ProcedureId, Statement, StatementId, VariableId,
};
use crate::propagation::partially_accessed_var;
use crate::semantic_analysis::validator::get_special_procedures;
use crate::semantic_analysis::GlobalInfo;
use crate::{Program, Target};

// MARK: Unreachable Procedures

enum WorkItem {
   Procedure(ProcedureId),
   Static(VariableId),
}

struct DceCtx<'a> {
   worklist: Vec<WorkItem>,
   global_info: &'a IndexMap<VariableId, GlobalInfo>,
   literals: &'a mut IndexSet<StrId>,
}

pub fn delete_unreachable_procedures_and_globals(program: &mut Program, interner: &mut Interner, target: Target) {
   let mut ctx: DceCtx<'_> = DceCtx {
      worklist: Vec::new(),
      global_info: &program.non_stack_var_info,
      literals: &mut program.literals,
   };

   let mut reachable_procedures: HashSet<ProcedureId> = HashSet::new();
   let mut reachable_globals: HashSet<VariableId> = HashSet::new();

   for special_proc in get_special_procedures(target, interner) {
      if let Some(proc_id) = program.procedure_name_table.get(&special_proc.name).copied() {
         ctx.worklist.push(WorkItem::Procedure(proc_id));
      }
   }

   for static_expr in program.non_stack_var_info.values().filter_map(|x| x.initializer) {
      mark_reachable_expr(static_expr, &program.ast, &mut ctx);
   }

   while let Some(reachable_item) = ctx.worklist.pop() {
      match reachable_item {
         WorkItem::Procedure(reachable_proc) => {
            if !reachable_procedures.insert(reachable_proc) {
               continue;
            }

            if let Some(body) = program.procedure_bodies.get_mut(reachable_proc) {
               mark_reachable_block(&body.block, &program.ast, &mut ctx);
            }
         }
         WorkItem::Static(reachable_global) => {
            if !reachable_globals.insert(reachable_global) {
               continue;
            }

            if let Some(val_expr) = program.non_stack_var_info[&reachable_global].initializer {
               mark_reachable_expr(val_expr, &program.ast, &mut ctx);
            }
         }
      }
   }

   program.procedures.retain(|k, _| reachable_procedures.contains(&k));
   program
      .procedure_bodies
      .retain(|k, _| program.procedures.contains_key(k));
   program.non_stack_var_info.retain(|k, _| reachable_globals.contains(k));
}

fn mark_reachable_block(block: &BlockNode, ast: &AstPool, ctx: &mut DceCtx) {
   for stmt in block.statements.iter().copied() {
      mark_reachable_stmt(stmt, ast, ctx);
   }
}

fn mark_reachable_stmt(stmt: StatementId, ast: &AstPool, ctx: &mut DceCtx) {
   match &ast.statements[stmt].statement {
      Statement::Assignment(lhs, rhs) => {
         mark_reachable_expr(*lhs, ast, ctx);
         mark_reachable_expr(*rhs, ast, ctx);
      }
      Statement::Block(bn) | Statement::Loop(bn) => {
         mark_reachable_block(bn, ast, ctx);
      }
      Statement::Expression(expr) | Statement::Return(expr) => {
         mark_reachable_expr(*expr, ast, ctx);
      }
      Statement::IfElse {
         cond,
         then,
         otherwise: else_s,
         constant: _,
      } => {
         mark_reachable_expr(*cond, ast, ctx);
         mark_reachable_block(then, ast, ctx);
         mark_reachable_stmt(*else_s, ast, ctx);
      }
      Statement::Continue | Statement::Break => (),
      Statement::VariableDeclaration { .. } | Statement::Defer(_) | Statement::For { .. } | Statement::While(_, _) => {
         unreachable!()
      }
   }
}

fn mark_reachable_expr(expr: ExpressionId, ast: &AstPool, ctx: &mut DceCtx) {
   match &ast.expressions[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_reachable_expr(*proc_expr, ast, ctx);
         for arg in args.iter() {
            mark_reachable_expr(arg.expr, ast, ctx);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            mark_reachable_expr(*expr, ast, ctx);
         }
      }
      Expression::ArrayIndex { array, index } => {
         mark_reachable_expr(*array, ast, ctx);
         mark_reachable_expr(*index, ast, ctx);
      }
      Expression::StringLiteral(lit) => {
         ctx.literals.insert(*lit);
      }
      Expression::Variable(var_id) => {
         if ctx.global_info.contains_key(var_id) {
            ctx.worklist.push(WorkItem::Static(*var_id));
         }
         // Local variables will be eliminated later
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         mark_reachable_expr(*lhs, ast, ctx);
         mark_reachable_expr(*rhs, ast, ctx);
      }
      Expression::UnaryOperator(_, operand) => {
         mark_reachable_expr(*operand, ast, ctx);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.values().flatten() {
            mark_reachable_expr(*field_expr, ast, ctx);
         }
      }
      Expression::FieldAccess(_, base) => {
         mark_reachable_expr(*base, ast, ctx);
      }
      Expression::Cast { expr, .. } => {
         mark_reachable_expr(*expr, ast, ctx);
      }
      Expression::IfX(a, b, c) => {
         mark_reachable_expr(*a, ast, ctx);
         mark_reachable_expr(*b, ast, ctx);
         mark_reachable_expr(*c, ast, ctx);
      }
      Expression::BoundFcnLiteral(id, _) => {
         ctx.worklist.push(WorkItem::Procedure(*id));
      }
      Expression::BoolLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral
      | Expression::EnumLiteral(_, _) => (),
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}

// MARK: Unused Variables
pub fn remove_unused_locals(program: &mut Program) {
   let mut used_vars: HashSet<VariableId> = HashSet::new();
   for (proc_id, proc_body) in program.procedure_bodies.iter_mut() {
      used_vars.clear();
      used_vars.reserve(proc_body.locals.len());

      let post_order = post_order(&proc_body.cfg);

      // Mark
      for bb_index in post_order.iter().copied().rev() {
         for instruction in proc_body.cfg.bbs[bb_index].instructions.iter() {
            match instruction {
               CfgInstruction::Assignment(lhs, rhs) => {
                  mark_used_vars_in_expr(*lhs, &mut used_vars, &program.ast.expressions, true);
                  mark_used_vars_in_expr(*rhs, &mut used_vars, &program.ast.expressions, false);
               }
               CfgInstruction::Expression(expr)
               | CfgInstruction::Return(expr)
               | CfgInstruction::ConditionalJump(expr, _, _) => {
                  mark_used_vars_in_expr(*expr, &mut used_vars, &program.ast.expressions, false);
               }
               CfgInstruction::Nop | CfgInstruction::Jump(_) => (),
            }
         }
      }

      // Sweep
      for bb_index in post_order.iter().copied().rev() {
         proc_body.cfg.bbs[bb_index].instructions.retain_mut(|instr| {
            if let CfgInstruction::Assignment(lhs, rhs) = instr {
               if let Some(v) = partially_accessed_var(*lhs, &program.ast.expressions) {
                  if !used_vars.contains(&v) && proc_body.locals.contains_key(&v) {
                     debug_assert!(!expression_could_have_side_effects(*lhs, &program.ast.expressions));
                     if expression_could_have_side_effects(*rhs, &program.ast.expressions) {
                        *instr = CfgInstruction::Expression(*rhs);
                     } else {
                        return false;
                     }
                  }
               }
            }
            true
         });
      }
      // extend used vars with parameters only after we killed assignments to unused ones
      used_vars.extend(
         program.procedures[proc_id]
            .definition
            .parameters
            .iter()
            .map(|x| x.var_id),
      );
      proc_body.locals.retain(|var, _| used_vars.contains(var));
   }
}

fn mark_used_vars_in_expr(
   in_expr: ExpressionId,
   used_vars: &mut HashSet<VariableId>,
   ast: &ExpressionPool,
   is_write: bool,
) {
   match &ast[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_used_vars_in_expr(*proc_expr, used_vars, ast, false);

         for val in args.iter().map(|x| x.expr) {
            mark_used_vars_in_expr(val, used_vars, ast, false);
         }
      }
      Expression::FieldAccess(_, base) => {
         mark_used_vars_in_expr(*base, used_vars, ast, is_write);
      }
      Expression::ArrayIndex { array, index } => {
         if expression_could_have_side_effects(*index, ast) {
            // conservatively, we consider any side effects in an index expression
            // disqualifying, since the subsequent transformation doesn't preserve
            // LHS side effects.
            // this should only be hittable in WASM, where we don't go into TAC
            mark_used_vars_in_expr(*array, used_vars, ast, false);
         } else {
            mark_used_vars_in_expr(*array, used_vars, ast, is_write);
         }
         mark_used_vars_in_expr(*index, used_vars, ast, false);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         mark_used_vars_in_expr(*lhs, used_vars, ast, false);
         mark_used_vars_in_expr(*rhs, used_vars, ast, false);
      }
      Expression::IfX(a, b, c) => {
         mark_used_vars_in_expr(*a, used_vars, ast, false);
         mark_used_vars_in_expr(*b, used_vars, ast, false);
         mark_used_vars_in_expr(*c, used_vars, ast, false);
      }
      Expression::Cast { expr, .. } | Expression::UnaryOperator(_, expr) => {
         mark_used_vars_in_expr(*expr, used_vars, ast, false);
      }
      Expression::Variable(v) => {
         if !is_write {
            used_vars.insert(*v);
         }
      }
      Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => (),
      Expression::ArrayLiteral(_)
      | Expression::StructLiteral(_, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}
