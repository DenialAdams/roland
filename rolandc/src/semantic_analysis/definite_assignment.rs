use std::collections::HashSet;

use indexmap::IndexMap;

use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::parse::{
   AstPool, BlockNode, DeclarationValue, Expression, ExpressionId, ProcImplSource, Statement, StatementId, VariableId,
};
use crate::type_data::ExpressionType;
use crate::Program;

pub fn ensure_variables_definitely_assigned(program: &Program, err_manager: &mut ErrorManager) {
   for procedure in program.procedures.values() {
      if let ProcImplSource::Body(block) = &procedure.proc_impl {
         let mut unassigned_vars: HashSet<VariableId> = procedure.locals.keys().copied().collect();
         for param in procedure.definition.parameters.iter() {
            unassigned_vars.remove(&param.var_id);
         }
         ensure_all_variables_assigned_in_block(
            block,
            &mut unassigned_vars,
            &procedure.locals,
            &program.ast,
            err_manager,
         );
      }
   }
}

fn ensure_all_variables_assigned_in_block(
   proc_body: &BlockNode,
   unassigned_vars: &mut HashSet<VariableId>,
   var_types: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   for stmt_id in proc_body.statements.iter().copied() {
      ensure_all_variables_assigned_in_stmt(stmt_id, unassigned_vars, var_types, pool, err_manager);
   }
}

fn ensure_all_variables_assigned_in_stmt(
   stmt_id: StatementId,
   unassigned_vars: &mut HashSet<VariableId>,
   var_types: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   let sn = &pool.statements[stmt_id];
   match &sn.statement {
      Statement::VariableDeclaration(_, decl_val, _, var_id) => match decl_val {
         DeclarationValue::Expr(e) => {
            ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, pool, err_manager);
            unassigned_vars.remove(&var_id);
         }
         DeclarationValue::Uninit => {
            unassigned_vars.remove(&var_id);
         }
         DeclarationValue::None => (),
      },
      Statement::Assignment(lhs, rhs) => {
         ensure_expression_does_not_use_unassigned_variable(*rhs, unassigned_vars, pool, err_manager);

         if let Expression::Variable(var_id) = pool.expressions[*lhs].expression {
            unassigned_vars.remove(&var_id);
         } else if let Expression::FieldAccess(_, inner_expr_id) = pool.expressions[*lhs].expression {
            if let Expression::Variable(var_id) = pool.expressions[inner_expr_id].expression {
               if let Some(ExpressionType::Union(_)) = var_types.get(&var_id) {
                  // Assigning one field of a union fully assigns the variable
                  unassigned_vars.remove(&var_id);
               }
            }
         }

         ensure_expression_does_not_use_unassigned_variable(*lhs, unassigned_vars, pool, err_manager);
      }
      Statement::Block(b) => {
         ensure_all_variables_assigned_in_block(&b, unassigned_vars, var_types, pool, err_manager);
      }
      Statement::IfElse(cond, then, otherwise) => {
         ensure_expression_does_not_use_unassigned_variable(*cond, unassigned_vars, pool, err_manager);

         let mut else_unassigned = unassigned_vars.clone();
         ensure_all_variables_assigned_in_block(&then, unassigned_vars, var_types, pool, err_manager);
         ensure_all_variables_assigned_in_stmt(*otherwise, &mut else_unassigned, var_types, pool, err_manager);

         // Union the then and else results
         unassigned_vars.extend(else_unassigned);
      }
      Statement::Loop(b) => {
         // We can't trust any assignment in a loop wihout more sophisticated dataflow analysis,
         // because continue and break may skip execution of assignments inside

         let backup = unassigned_vars.clone();
         ensure_all_variables_assigned_in_block(&b, unassigned_vars, var_types, pool, err_manager);
         *unassigned_vars = backup;
      }
      Statement::Expression(e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, pool, err_manager);
      }
      Statement::Return(e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, pool, err_manager);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::For { .. } => unreachable!(),
      Statement::While(_, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
   }
}

fn ensure_expression_does_not_use_unassigned_variable(
   expr_id: ExpressionId,
   unassigned_vars: &mut HashSet<VariableId>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   let en = &pool.expressions[expr_id];
   match &en.expression {
      Expression::Variable(var_id) => {
         if unassigned_vars.contains(var_id) {
            rolandc_error!(
               err_manager,
               en.location,
               "Variable may not have been assigned at this use"
            );
            // To avoid spamming with errors, pretend it has been assigned
            unassigned_vars.remove(var_id);
         }
      }
      Expression::ProcedureCall { proc_expr, args } => {
         ensure_expression_does_not_use_unassigned_variable(*proc_expr, unassigned_vars, pool, err_manager);
         for arg in args.iter() {
            ensure_expression_does_not_use_unassigned_variable(arg.expr, unassigned_vars, pool, err_manager);
         }
      }
      Expression::ArrayLiteral(items) => {
         for item in items.iter().copied() {
            ensure_expression_does_not_use_unassigned_variable(item, unassigned_vars, pool, err_manager);
         }
      }
      Expression::ArrayIndex { array, index } => {
         ensure_expression_does_not_use_unassigned_variable(*array, unassigned_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*index, unassigned_vars, pool, err_manager);
      }
      Expression::BinaryOperator { operator: _, lhs, rhs } => {
         ensure_expression_does_not_use_unassigned_variable(*lhs, unassigned_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*rhs, unassigned_vars, pool, err_manager);
      }
      Expression::UnaryOperator(_, e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, pool, err_manager);
      }
      Expression::IfX(a, b, c) => {
         ensure_expression_does_not_use_unassigned_variable(*a, unassigned_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*b, unassigned_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*c, unassigned_vars, pool, err_manager);
      }
      Expression::StructLiteral(_, fields) => {
         for e in fields.iter().flat_map(|x| x.1) {
            ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, pool, err_manager);
         }
      }
      Expression::FieldAccess(_, e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, pool, err_manager);
      }
      Expression::Cast { expr, .. } => {
         ensure_expression_does_not_use_unassigned_variable(*expr, unassigned_vars, pool, err_manager);
      }
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(_, _) => (),
      Expression::UnresolvedEnumLiteral(_, _)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedStructLiteral(_, _) => unreachable!(),
   }
}
