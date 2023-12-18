use bitvec::bitbox;
use bitvec::boxed::BitBox;
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
         let mut unassigned_vars: BitBox = bitbox![1; procedure.locals.len()];
         for param in procedure.definition.parameters.iter() {
            unassigned_vars.set(procedure.locals.get_index_of(&param.var_id).unwrap(), false);
         }
         ensure_all_variables_assigned_in_block(
            block,
            &mut unassigned_vars,
            &mut None,
            &procedure.locals,
            &program.ast,
            err_manager,
         );
      }
   }
}

fn ensure_all_variables_assigned_in_block(
   block: &BlockNode,
   unassigned_vars: &mut BitBox,
   unassigned_vars_after_loop: &mut Option<BitBox>,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   for stmt_id in block.statements.iter().copied() {
      ensure_all_variables_assigned_in_stmt(
         stmt_id,
         unassigned_vars,
         unassigned_vars_after_loop,
         procedure_vars,
         pool,
         err_manager,
      );
   }
}

fn ensure_all_variables_assigned_in_stmt(
   stmt_id: StatementId,
   unassigned_vars: &mut BitBox,
   unassigned_vars_after_loop: &mut Option<BitBox>,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   let sn = &pool.statements[stmt_id];
   match &sn.statement {
      Statement::VariableDeclaration(_, decl_val, _, var_id) => match decl_val {
         DeclarationValue::Expr(e) => {
            ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, procedure_vars, pool, err_manager);
            if let Some(index) = procedure_vars.get_index_of(var_id) {
               unassigned_vars.set(index, false);
            }
         }
         DeclarationValue::Uninit => {
            if let Some(index) = procedure_vars.get_index_of(var_id) {
               unassigned_vars.set(index, false);
            }
         }
         DeclarationValue::None => (),
      },
      Statement::Assignment(lhs, rhs) => {
         ensure_expression_does_not_use_unassigned_variable(*rhs, unassigned_vars, procedure_vars, pool, err_manager);

         if let Expression::Variable(var_id) = pool.expressions[*lhs].expression {
            if let Some(index) = procedure_vars.get_index_of(&var_id) {
               unassigned_vars.set(index, false);
            }
         } else if let Expression::FieldAccess(_, inner_expr_id) = pool.expressions[*lhs].expression {
            if let Expression::Variable(var_id) = pool.expressions[inner_expr_id].expression {
               if let Some(ExpressionType::Union(_)) = procedure_vars.get(&var_id) {
                  // Assigning one field of a union fully assigns the variable
                  if let Some(index) = procedure_vars.get_index_of(&var_id) {
                     unassigned_vars.set(index, false);
                  }
               }
            }
         }

         ensure_expression_does_not_use_unassigned_variable(*lhs, unassigned_vars, procedure_vars, pool, err_manager);
      }
      Statement::Block(b) => {
         ensure_all_variables_assigned_in_block(
            b,
            unassigned_vars,
            unassigned_vars_after_loop,
            procedure_vars,
            pool,
            err_manager,
         );
      }
      Statement::IfElse(cond, then, otherwise) => {
         ensure_expression_does_not_use_unassigned_variable(*cond, unassigned_vars, procedure_vars, pool, err_manager);

         let mut else_unassigned = unassigned_vars.clone();
         ensure_all_variables_assigned_in_block(
            then,
            unassigned_vars,
            unassigned_vars_after_loop,
            procedure_vars,
            pool,
            err_manager,
         );
         ensure_all_variables_assigned_in_stmt(
            *otherwise,
            &mut else_unassigned,
            unassigned_vars_after_loop,
            procedure_vars,
            pool,
            err_manager,
         );

         *unassigned_vars |= else_unassigned;
      }
      Statement::Loop(b) => {
         let mut unassigned_after_new_loop = Some(bitbox![0; procedure_vars.len()]);
         ensure_all_variables_assigned_in_block(
            b,
            unassigned_vars,
            &mut unassigned_after_new_loop,
            procedure_vars,
            pool,
            err_manager,
         );
         *unassigned_vars = unassigned_after_new_loop.unwrap();
      }
      Statement::Expression(e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, procedure_vars, pool, err_manager);
         if *pool.expressions[*e].exp_type.as_ref().unwrap() == ExpressionType::Never {
            unassigned_vars.fill(false);
         }
      }
      Statement::Return(e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, procedure_vars, pool, err_manager);
         unassigned_vars.fill(false);
      }
      Statement::Continue => unassigned_vars.fill(false),
      Statement::Break => {
         *unassigned_vars_after_loop.as_mut().unwrap() |= unassigned_vars.as_bitslice();
         unassigned_vars.fill(false);
      }
      Statement::For { .. } => unreachable!(),
      Statement::While(_, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
   }
}

fn ensure_expression_does_not_use_unassigned_variable(
   expr_id: ExpressionId,
   unassigned_vars: &mut BitBox,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   pool: &AstPool,
   err_manager: &mut ErrorManager,
) {
   let en = &pool.expressions[expr_id];
   match &en.expression {
      Expression::Variable(var_id) => {
         if let Some(index) = procedure_vars.get_index_of(var_id) {
            if unassigned_vars[index] {
               rolandc_error!(
                  err_manager,
                  en.location,
                  "Variable may not have been assigned at this use"
               );
               // To avoid spamming with errors, pretend it has been assigned
               unassigned_vars.set(index, false);
            }
         }
      }
      Expression::ProcedureCall { proc_expr, args } => {
         ensure_expression_does_not_use_unassigned_variable(*proc_expr, unassigned_vars, procedure_vars, pool, err_manager);
         for arg in args.iter() {
            ensure_expression_does_not_use_unassigned_variable(arg.expr, unassigned_vars, procedure_vars, pool, err_manager);
         }
      }
      Expression::ArrayLiteral(items) => {
         for item in items.iter().copied() {
            ensure_expression_does_not_use_unassigned_variable(item, unassigned_vars, procedure_vars, pool, err_manager);
         }
      }
      Expression::ArrayIndex { array, index } => {
         ensure_expression_does_not_use_unassigned_variable(*array, unassigned_vars, procedure_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*index, unassigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::BinaryOperator { operator: _, lhs, rhs } => {
         ensure_expression_does_not_use_unassigned_variable(*lhs, unassigned_vars, procedure_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*rhs, unassigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::UnaryOperator(_, e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::IfX(a, b, c) => {
         ensure_expression_does_not_use_unassigned_variable(*a, unassigned_vars, procedure_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*b, unassigned_vars, procedure_vars, pool, err_manager);
         ensure_expression_does_not_use_unassigned_variable(*c, unassigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::StructLiteral(_, fields) => {
         for e in fields.iter().flat_map(|x| x.1) {
            ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, procedure_vars, pool, err_manager);
         }
      }
      Expression::FieldAccess(_, e) => {
         ensure_expression_does_not_use_unassigned_variable(*e, unassigned_vars, procedure_vars, pool, err_manager);
      }
      Expression::Cast { expr, .. } => {
         ensure_expression_does_not_use_unassigned_variable(*expr, unassigned_vars, procedure_vars, pool, err_manager);
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
