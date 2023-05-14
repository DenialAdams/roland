use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use crate::interner::{Interner, StrId};
use crate::parse::{AstPool, BlockNode, Expression, ExpressionId, Statement, StatementId, StaticId, VariableId};
use crate::semantic_analysis::validator::get_special_procedures;
use crate::semantic_analysis::{GlobalInfo, GlobalKind, ProcImplSource};
use crate::{Program, Target};

type ProcedureId = StrId;

enum WorkItem {
   Procedure(ProcedureId),
   Static(StaticId),
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
   let mut reachable_globals: HashSet<StaticId> = HashSet::new();

   for special_proc in get_special_procedures(target, interner) {
      if program.procedure_info.contains_key(&special_proc.name) {
         ctx.worklist.push(WorkItem::Procedure(special_proc.name));
      }
   }

   for static_expr in program.statics.values().flat_map(|x| x.value) {
      mark_reachable_expr(static_expr, &program.ast, &mut ctx);
   }

   while let Some(reachable_item) = ctx.worklist.pop() {
      match reachable_item {
         WorkItem::Procedure(reachable_proc) => {
            if reachable_procedures.contains(&reachable_proc) {
               continue;
            }

            reachable_procedures.insert(reachable_proc);

            if let ProcImplSource::ProcedureId(proc_id) =
               program.procedure_info.get(&reachable_proc).unwrap().proc_impl_source
            {
               let pn = program.procedures.get(proc_id).unwrap();
               mark_reachable_block(&pn.block, &program.ast, &mut ctx);
            }
         }
         WorkItem::Static(reachable_global) => {
            if reachable_globals.contains(&reachable_global) {
               continue;
            }

            reachable_globals.insert(reachable_global);

            if let Some(val_expr) = program.statics[reachable_global].value {
               mark_reachable_expr(val_expr, &program.ast, &mut ctx);
            }
         }
      }
   }

   program
      .procedures
      .retain(|_, x| reachable_procedures.contains(&x.definition.name));
   program
      .external_procedures
      .retain(|x| reachable_procedures.contains(&x.definition.name));
   program.statics.retain(|k, _| reachable_globals.contains(&k));
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
      Statement::For {
         induction_var_name: _,
         range_start: start,
         range_end: end,
         body: bn,
         range_inclusive: _,
         induction_var: _,
      } => {
         mark_reachable_expr(*start, ast, ctx);
         mark_reachable_expr(*end, ast, ctx);
         mark_reachable_block(bn, ast, ctx);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::Defer(_) => unreachable!(),
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
      Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
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
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::Variable(var_id) => {
         if let Some(GlobalKind::Static(static_id)) = ctx.global_info.get(var_id).map(|x| &x.kind) {
            ctx.worklist.push(WorkItem::Static(*static_id));
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
         for field_expr in field_exprs.iter() {
            mark_reachable_expr(field_expr.1, ast, ctx);
         }
      }
      Expression::FieldAccess(_, base) => {
         mark_reachable_expr(*base, ast, ctx);
      }
      Expression::Cast { expr, .. } => {
         mark_reachable_expr(*expr, ast, ctx);
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(id, _) => {
         ctx.worklist.push(WorkItem::Procedure(id.str));
      }
   }
}
