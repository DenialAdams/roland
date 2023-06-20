use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ProcImplSource, ProcedureId, Statement, StatementId, VariableId,
};
use crate::semantic_analysis::validator::get_special_procedures;
use crate::semantic_analysis::GlobalInfo;
use crate::{Program, Target};

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
   let mut ctx = DceCtx {
      worklist: Vec::new(),
      global_info: &program.global_info,
      literals: &mut program.literals,
   };

   let mut reachable_procedures: HashSet<ProcedureId> = HashSet::new();
   let mut reachable_globals: HashSet<VariableId> = HashSet::new();

   for special_proc in get_special_procedures(target, interner) {
      if let Some(proc_id) = program.procedure_name_table.get(&special_proc.name).copied() {
         ctx.worklist.push(WorkItem::Procedure(proc_id));
      }
   }

   for static_expr in program.global_info.values().flat_map(|x| x.initializer) {
      mark_reachable_expr(static_expr, &program.ast, &mut ctx);
   }

   while let Some(reachable_item) = ctx.worklist.pop() {
      match reachable_item {
         WorkItem::Procedure(reachable_proc) => {
            if reachable_procedures.contains(&reachable_proc) {
               continue;
            }

            reachable_procedures.insert(reachable_proc);

            if let ProcImplSource::Body(block) = &program.procedures.get(reachable_proc).unwrap().proc_impl {
               mark_reachable_block(block, &program.ast, &mut ctx);
            }
         }
         WorkItem::Static(reachable_global) => {
            if reachable_globals.contains(&reachable_global) {
               continue;
            }

            reachable_globals.insert(reachable_global);

            if let Some(val_expr) = program.global_info[&reachable_global].initializer {
               mark_reachable_expr(val_expr, &program.ast, &mut ctx);
            }
         }
      }
   }

   program.procedures.retain(|k, _| reachable_procedures.contains(&k));
   program.global_info.retain(|k, _| reachable_globals.contains(k));
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
      Statement::Block(bn) => {
         mark_reachable_block(bn, ast, ctx);
      }
      Statement::Loop(bn) => {
         mark_reachable_block(bn, ast, ctx);
      }
      Statement::Expression(expr) => {
         mark_reachable_expr(*expr, ast, ctx);
      }
      Statement::IfElse(cond, then, else_s) => {
         mark_reachable_expr(*cond, ast, ctx);
         mark_reachable_block(then, ast, ctx);
         mark_reachable_stmt(*else_s, ast, ctx);
      }
      Statement::Return(expr) => {
         mark_reachable_expr(*expr, ast, ctx);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
      Statement::For { .. } => unreachable!(),
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
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(lit) => {
         ctx.literals.insert(*lit);
      }
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::Variable(var_id) => {
         if ctx.global_info.contains_key(var_id) {
            ctx.worklist.push(WorkItem::Static(*var_id));
         }
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
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(id, _) => {
         ctx.worklist.push(WorkItem::Procedure(*id));
      }
      Expression::UnresolvedVariable(_) | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) => unreachable!(),
   }
}
