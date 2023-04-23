use std::collections::HashSet;

use crate::interner::{Interner, StrId};
use crate::parse::{BlockNode, Expression, ExpressionId, ExpressionPool, Statement};
use crate::semantic_analysis::validator::get_special_procedures;
use crate::semantic_analysis::ProcImplSource;
use crate::{Program, Target};

type ProcedureId = StrId;

pub fn doit(program: &mut Program, interner: &mut Interner, target: Target) {
   let mut worklist: Vec<ProcedureId> = Vec::new();
   let mut reachable_procedures: HashSet<ProcedureId> = HashSet::new();

   for special_proc in get_special_procedures(target, interner) {
      if program.procedure_info.contains_key(&special_proc.name) {
         worklist.push(special_proc.name);
      }
   }

   for static_expr in program.statics.iter().flat_map(|x| x.value) {
      mark_reachable_expr(static_expr, &program.expressions, &mut worklist);
   }

   while let Some(reachable_proc) = worklist.pop() {
      if reachable_procedures.contains(&reachable_proc) {
         continue;
      }

      reachable_procedures.insert(reachable_proc);

      if let ProcImplSource::ProcedureId(proc_id) =
         program.procedure_info.get(&reachable_proc).unwrap().proc_impl_source
      {
         let pn = program.procedures.get(proc_id).unwrap();
         mark_reachable_block(&pn.block, &program.expressions, &mut worklist);
      }
   }

   program
      .procedures
      .retain(|x| reachable_procedures.contains(&x.definition.name));
   program
      .external_procedures
      .retain(|x| reachable_procedures.contains(&x.definition.name));
}

fn mark_reachable_block(block: &BlockNode, expressions: &ExpressionPool, worklist: &mut Vec<ProcedureId>) {
   for stmt in block.statements.iter() {
      mark_reachable_stmt(&stmt.statement, expressions, worklist);
   }
}

fn mark_reachable_stmt(stmt: &Statement, expressions: &ExpressionPool, worklist: &mut Vec<ProcedureId>) {
   match stmt {
      Statement::Assignment(lhs, rhs) => {
         mark_reachable_expr(*lhs, expressions, worklist);
         mark_reachable_expr(*rhs, expressions, worklist);
      }
      Statement::Block(bn) => {
         mark_reachable_block(bn, expressions, worklist);
      }
      Statement::Loop(bn) => {
         mark_reachable_block(bn, expressions, worklist);
      }
      Statement::For(_, start, end, bn, _, _) => {
         mark_reachable_expr(*start, expressions, worklist);
         mark_reachable_expr(*end, expressions, worklist);
         mark_reachable_block(bn, expressions, worklist);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::Expression(expr) => {
         mark_reachable_expr(*expr, expressions, worklist);
      }
      Statement::IfElse(cond, then, else_e) => {
         mark_reachable_expr(*cond, expressions, worklist);
         mark_reachable_block(then, expressions, worklist);
         mark_reachable_stmt(&else_e.statement, expressions, worklist);
      }
      Statement::Return(expr) => {
         mark_reachable_expr(*expr, expressions, worklist);
      }
      Statement::VariableDeclaration(_, initializer, _, _) => {
         if let Some(initializer) = initializer.as_ref() {
            mark_reachable_expr(*initializer, expressions, worklist);
         }
      }
   }
}

fn mark_reachable_expr(expr: ExpressionId, expressions: &ExpressionPool, worklist: &mut Vec<ProcedureId>) {
   let mut cloned = expressions[expr].clone();
   match &mut cloned.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_reachable_expr(*proc_expr, expressions, worklist);
         for arg in args.iter_mut() {
            mark_reachable_expr(arg.expr, expressions, worklist);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            mark_reachable_expr(*expr, expressions, worklist);
         }
      }
      Expression::ArrayIndex { array, index } => {
         mark_reachable_expr(*array, expressions, worklist);
         mark_reachable_expr(*index, expressions, worklist);
      }
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::Variable(_) => (),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         mark_reachable_expr(*lhs, expressions, worklist);
         mark_reachable_expr(*rhs, expressions, worklist);
      }
      Expression::UnaryOperator(_, operand) => {
         mark_reachable_expr(*operand, expressions, worklist);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.iter_mut() {
            mark_reachable_expr(field_expr.1, expressions, worklist);
         }
      }
      Expression::FieldAccess(_, base) => {
         mark_reachable_expr(*base, expressions, worklist);
      }
      Expression::Cast { expr, .. } => {
         mark_reachable_expr(*expr, expressions, worklist);
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(id, _) => {
         worklist.push(id.str);
      }
   }
}
