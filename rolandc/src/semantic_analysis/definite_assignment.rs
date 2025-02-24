use bitvec::bitbox;
use bitvec::boxed::BitBox;
use bitvec::slice::BitSlice;
use bitvec::vec::BitVec;
use indexmap::IndexMap;

use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::parse::{
   AstPool, BlockNode, DeclarationValue, Expression, ExpressionId, Statement, StatementId, VariableId,
};
use crate::type_data::ExpressionType;
use crate::Program;

pub fn ensure_variables_definitely_assigned(program: &Program, err_manager: &mut ErrorManager) {
   let mut assigned_vars: BitVec = BitVec::new();
   for (id, body) in program.procedure_bodies.iter() {
      assigned_vars.clear();
      assigned_vars.reserve(body.locals.len());
      assigned_vars.extend(std::iter::repeat_n(false, body.locals.len()));
      for param in program.procedures[id].definition.parameters.iter() {
         assigned_vars.set(body.locals.get_index_of(&param.var_id).unwrap(), true);
      }
      ensure_all_variables_assigned_in_block(
         &body.block,
         &mut assigned_vars,
         &mut None,
         &body.locals,
         &program.ast,
         err_manager,
      );
   }
}

fn ensure_all_variables_assigned_in_block(
   block: &BlockNode,
   assigned_vars: &mut BitSlice,
   assigned_vars_after_loop: &mut Option<BitBox>,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   for stmt_id in block.statements.iter().copied() {
      ensure_all_variables_assigned_in_stmt(
         stmt_id,
         assigned_vars,
         assigned_vars_after_loop,
         procedure_vars,
         pool,
         err_manager,
      );
   }
}

fn ensure_all_variables_assigned_in_stmt(
   stmt_id: StatementId,
   assigned_vars: &mut BitSlice,
   assigned_vars_after_loop: &mut Option<BitBox>,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   let sn = &pool.statements[stmt_id];
   match &sn.statement {
      Statement::VariableDeclaration {
         var_name: _,
         value: decl_val,
         declared_type: _,
         var_id,
         storage: _,
      } => match decl_val {
         DeclarationValue::Expr(e) => {
            ensure_expression_does_not_use_unassigned_variable(*e, assigned_vars, procedure_vars, pool, err_manager);
            if let Some(index) = procedure_vars.get_index_of(var_id) {
               assigned_vars.set(index, true);
            }
         }
         DeclarationValue::Uninit => {
            if let Some(index) = procedure_vars.get_index_of(var_id) {
               assigned_vars.set(index, true);
            }
         }
         DeclarationValue::None => (),
      },
      Statement::Assignment(lhs, rhs) => {
         ensure_expression_does_not_use_unassigned_variable(*rhs, assigned_vars, procedure_vars, pool, err_manager);

         if let Expression::Variable(var_id) = pool.expressions[*lhs].expression {
            if let Some(index) = procedure_vars.get_index_of(&var_id) {
               assigned_vars.set(index, true);
            }
         } else if let Expression::FieldAccess(_, inner_expr_id) = pool.expressions[*lhs].expression {
            if let Expression::Variable(var_id) = pool.expressions[inner_expr_id].expression {
               if let Some(ExpressionType::Union(_, _)) = procedure_vars.get(&var_id) {
                  // Assigning one field of a union fully assigns the variable
                  if let Some(index) = procedure_vars.get_index_of(&var_id) {
                     assigned_vars.set(index, true);
                  }
               }
            }
         }

         ensure_expression_does_not_use_unassigned_variable(*lhs, assigned_vars, procedure_vars, pool, err_manager);
      }
      Statement::Block(b) => {
         ensure_all_variables_assigned_in_block(
            b,
            assigned_vars,
            assigned_vars_after_loop,
            procedure_vars,
            pool,
            err_manager,
         );
      }
      Statement::IfElse {
         cond,
         then,
         otherwise,
         constant: _,
      } => {
         ensure_expression_does_not_use_unassigned_variable(*cond, assigned_vars, procedure_vars, pool, err_manager);

         let mut else_unassigned = assigned_vars.to_owned();
         ensure_all_variables_assigned_in_block(
            then,
            assigned_vars,
            assigned_vars_after_loop,
            procedure_vars,
            pool,
            err_manager,
         );
         ensure_all_variables_assigned_in_stmt(
            *otherwise,
            &mut else_unassigned,
            assigned_vars_after_loop,
            procedure_vars,
            pool,
            err_manager,
         );

         *assigned_vars &= else_unassigned;
      }
      Statement::Loop(b) => {
         let mut assigned_after_new_loop = Some(bitbox![1; procedure_vars.len()]);
         ensure_all_variables_assigned_in_block(
            b,
            assigned_vars,
            &mut assigned_after_new_loop,
            procedure_vars,
            pool,
            err_manager,
         );
         assigned_vars.clone_from_bitslice(assigned_after_new_loop.unwrap().as_bitslice());
      }
      Statement::Expression(e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, assigned_vars, procedure_vars, pool, err_manager);
         if *pool.expressions[*e].exp_type.as_ref().unwrap() == ExpressionType::Never {
            assigned_vars.fill(true);
         }
      }
      Statement::Return(e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, assigned_vars, procedure_vars, pool, err_manager);
         assigned_vars.fill(true);
      }
      Statement::Continue => assigned_vars.fill(true),
      Statement::Break => {
         *assigned_vars_after_loop.as_mut().unwrap() &= &*assigned_vars;
         assigned_vars.fill(true);
      }
      Statement::For { .. } | Statement::While(_, _) | Statement::Defer(_) => unreachable!(),
   }
}

fn ensure_expression_does_not_use_unassigned_variable(
   expr_id: ExpressionId,
   assigned_vars: &mut BitSlice,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   let en = &pool.expressions[expr_id];
   match &en.expression {
      Expression::Variable(var_id) => {
         if let Some(index) = procedure_vars.get_index_of(var_id) {
            if !assigned_vars[index] {
               rolandc_error!(
                  err_manager,
                  en.location,
                  "Variable may not have been assigned at this use"
               );
               // To avoid spamming with errors, pretend it has been assigned
               assigned_vars.set(index, true);
            }
         }
      }
      Expression::ProcedureCall { proc_expr, args } => {
         ensure_expression_does_not_use_unassigned_variable(
            *proc_expr,
            assigned_vars,
            procedure_vars,
            pool,
            err_manager,
         );
         for arg in args.iter() {
            ensure_expression_does_not_use_unassigned_variable(
               arg.expr,
               assigned_vars,
               procedure_vars,
               pool,
               err_manager,
            );
         }
      }
      Expression::ArrayLiteral(items) => {
         for item in items.iter().copied() {
            ensure_expression_does_not_use_unassigned_variable(item, assigned_vars, procedure_vars, pool, err_manager);
         }
      }
      Expression::ArrayIndex { array: a, index: b }
      | Expression::BinaryOperator {
         operator: _,
         lhs: a,
         rhs: b,
      } => {
         ensure_expression_does_not_use_unassigned_variable(*a, assigned_vars, procedure_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*b, assigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::IfX(a, b, c) => {
         ensure_expression_does_not_use_unassigned_variable(*a, assigned_vars, procedure_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*b, assigned_vars, procedure_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*c, assigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::StructLiteral(_, fields) => {
         for e in fields.iter().flat_map(|x| x.1) {
            ensure_expression_does_not_use_unassigned_variable(*e, assigned_vars, procedure_vars, pool, err_manager);
         }
      }
      Expression::FieldAccess(_, e) | Expression::UnaryOperator(_, e) | Expression::Cast { expr: e, .. } => {
         ensure_expression_does_not_use_unassigned_variable(*e, assigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral
      | Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _) => (),
      Expression::UnresolvedEnumLiteral(_, _)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedStructLiteral(_, _, _) => unreachable!(),
   }
}
