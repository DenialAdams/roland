use slotmap::SecondaryMap;

use super::OwnedValidationContext;
use super::type_variables::{TypeConstraint, TypeVariableManager};
use crate::error_handling::ErrorManager;
use crate::error_handling::error_handling_macros::rolandc_error_w_details;
use crate::parse::{Expression, ExpressionId, ExpressionPool, ProcedureBody, ProcedureId};
use crate::type_data::{ExpressionType, IntType};

fn constraint_compatible_with_concrete(constraint: TypeConstraint, concrete: &ExpressionType) -> bool {
   match constraint {
      TypeConstraint::None => true,
      TypeConstraint::Float => matches!(concrete, ExpressionType::Float(_)),
      TypeConstraint::SignedInt => matches!(concrete, ExpressionType::Int(IntType { signed: true, .. })),
      TypeConstraint::Int => matches!(concrete, ExpressionType::Int(_)),
      TypeConstraint::Enum => matches!(concrete, ExpressionType::Enum(_)),
   }
}

pub fn constraint_matches_type_or_try_constrain(
   constraint: TypeConstraint,
   the_type: &ExpressionType,
   type_variables: &mut TypeVariableManager,
) -> bool {
   if let ExpressionType::Unknown(u) = the_type {
      type_variables.get_data_mut(*u).add_constraint(constraint).is_ok()
   } else {
      constraint_compatible_with_concrete(constraint, the_type)
   }
}

pub fn try_merge_types(
   current_type: &ExpressionType,
   incoming_type: &ExpressionType,
   type_variables: &mut TypeVariableManager,
) -> bool {
   match (current_type, incoming_type) {
      (ExpressionType::Array(current_base, current_len), ExpressionType::Array(incoming_base, incoming_len)) => {
         if current_len != incoming_len {
            return false;
         }
         try_merge_types(current_base, incoming_base, type_variables)
      }
      (ExpressionType::Pointer(current_base), ExpressionType::Pointer(incoming_base)) => {
         try_merge_types(current_base, incoming_base, type_variables)
      }
      (
         ExpressionType::Struct(current_base, current_type_arguments),
         ExpressionType::Struct(incoming_base, incoming_type_arguments),
      ) => {
         if current_base != incoming_base {
            return false;
         }
         current_type_arguments
            .iter()
            .zip(incoming_type_arguments)
            .all(|(x, y)| try_merge_types(x, y, type_variables))
      }
      (
         ExpressionType::Union(current_base, current_type_arguments),
         ExpressionType::Union(incoming_base, incoming_type_arguments),
      ) => {
         if current_base != incoming_base {
            return false;
         }
         current_type_arguments
            .iter()
            .zip(incoming_type_arguments)
            .all(|(x, y)| try_merge_types(x, y, type_variables))
      }
      (
         ExpressionType::ProcedurePointer {
            parameters: current_parameters,
            ret_type: current_ret_type,
            variadic: _,
         },
         ExpressionType::ProcedurePointer {
            parameters: incoming_parameters,
            ret_type: incoming_ret_type,
            variadic: _,
         },
      ) => {
         if current_parameters.len() != incoming_parameters.len() {
            return false;
         }
         current_parameters
            .iter()
            .zip(incoming_parameters)
            .chain(std::iter::once((current_ret_type.as_ref(), incoming_ret_type.as_ref())))
            .all(|(x, y)| try_merge_types(x, y, type_variables))
      }
      (ExpressionType::Unknown(current_tv), ExpressionType::Unknown(incoming_tv)) => {
         type_variables.union(*current_tv, *incoming_tv).is_ok()
      }
      (ExpressionType::Unknown(tv), known_type) | (known_type, ExpressionType::Unknown(tv)) => {
         let data = type_variables.get_data_mut(*tv);
         if let Some(kt) = data.known_type.as_ref() {
            return kt == known_type;
         }
         if !constraint_compatible_with_concrete(data.constraint, known_type) {
            return false;
         }
         data.known_type = Some(known_type.clone());
         true
      }
      (current_type, incoming_type) => current_type == incoming_type,
   }
}

pub fn lower_type_variables(
   ctx: &mut OwnedValidationContext,
   procedure_bodies: &mut SecondaryMap<ProcedureId, ProcedureBody>,
   expressions: &mut ExpressionPool,
   err_manager: &mut ErrorManager,
) {
   let mut unknown_literals: Vec<ExpressionId> = Vec::new();
   for (i, e) in expressions.iter_mut() {
      if let Some(exp_type) = e.exp_type.as_mut() {
         lower_unknowns_in_type(exp_type, &ctx.type_variables);
         if matches!(
            e.expression,
            Expression::IntLiteral { .. }
               | Expression::FloatLiteral(_)
               | Expression::BoundFcnLiteral(_, _)
               | Expression::StructLiteral(_, _)
               | Expression::ArrayLiteral(_)
         ) && !exp_type.is_concrete_shallow()
         {
            unknown_literals.push(i);
         }
      }
      if let Expression::BoundFcnLiteral(_, type_arguments) = &mut e.expression {
         for type_arg in type_arguments.iter_mut() {
            lower_unknowns_in_type(&mut type_arg.e_type, &ctx.type_variables);
         }
      }
   }

   if !unknown_literals.is_empty() {
      let err_details: Vec<_> = unknown_literals
         .iter()
         .map(|x| {
            let loc = expressions[*x].location;
            (loc, "literal")
         })
         .collect();
      rolandc_error_w_details!(
         err_manager,
         &err_details,
         "We weren't able to determine the types of {} literals",
         unknown_literals.len()
      );
   }

   for body in procedure_bodies.values_mut() {
      for lt in body.locals.values_mut() {
         lower_unknowns_in_type(lt, &ctx.type_variables);
      }
   }
}

pub fn lower_unknowns_in_type(e: &mut ExpressionType, type_variables: &TypeVariableManager) {
   match e {
      ExpressionType::Unknown(tv) => {
         if let Some(new_type) = &type_variables.get_data(*tv).known_type {
            *e = new_type.clone();
            if !new_type.is_concrete() {
               lower_unknowns_in_type(e, type_variables);
            }
         }
      }
      ExpressionType::Pointer(base) | ExpressionType::Array(base, _) => lower_unknowns_in_type(base, type_variables),
      ExpressionType::ProcedureItem(_, type_arguments)
      | ExpressionType::Struct(_, type_arguments)
      | ExpressionType::Union(_, type_arguments) => {
         for t_arg in type_arguments.iter_mut() {
            lower_unknowns_in_type(t_arg, type_variables);
         }
      }
      ExpressionType::ProcedurePointer {
         parameters,
         ret_type,
         variadic: _,
      } => {
         for p in parameters {
            lower_unknowns_in_type(p, type_variables);
         }
         lower_unknowns_in_type(ret_type, type_variables);
      }
      _ => (),
   }
}

fn well_typed(et: &mut ExpressionType, type_variables: &TypeVariableManager) -> bool {
   lower_unknowns_in_type(et, type_variables);
   match et {
      ExpressionType::Unknown(_)
      | ExpressionType::CompileError
      | ExpressionType::GenericParam(_)
      | ExpressionType::Unresolved { .. } => false,
      ExpressionType::Pointer(v) | ExpressionType::Array(v, _) => well_typed(v, type_variables),
      ExpressionType::ProcedureItem(_, type_args)
      | ExpressionType::Struct(_, type_args)
      | ExpressionType::Union(_, type_args) => type_args.iter_mut().all(|t| well_typed(t, type_variables)),
      ExpressionType::ProcedurePointer {
         parameters,
         ret_type,
         variadic: _,
      } => parameters
         .iter_mut()
         .chain(std::iter::once(ret_type.as_mut()))
         .all(|t| well_typed(t, type_variables)),
      ExpressionType::Never
      | ExpressionType::Int(_)
      | ExpressionType::Float(_)
      | ExpressionType::Bool
      | ExpressionType::Unit
      | ExpressionType::Enum(_) => true,
   }
}

pub fn tree_is_well_typed(
   expr_id: ExpressionId,
   expressions: &mut ExpressionPool,
   type_variable_info: &TypeVariableManager,
) -> bool {
   let mut the_expr = std::mem::replace(&mut expressions[expr_id].expression, Expression::UnitLiteral);
   let children_ok = match &mut the_expr {
      Expression::ProcedureCall { proc_expr, args } => args
         .iter_mut()
         .map(|x| x.expr)
         .chain(std::iter::once(*proc_expr))
         .all(|x| tree_is_well_typed(x, expressions, type_variable_info)),
      Expression::ArrayLiteral(expression_ids) => expression_ids
         .iter_mut()
         .all(|x| tree_is_well_typed(*x, expressions, type_variable_info)),
      Expression::BinaryOperator { operator: _, lhs, rhs } | Expression::ArrayIndex { array: lhs, index: rhs } => {
         tree_is_well_typed(*lhs, expressions, type_variable_info)
            && tree_is_well_typed(*rhs, expressions, type_variable_info)
      }
      Expression::UnaryOperator(_, expression_id) | Expression::FieldAccess(_, expression_id) => {
         tree_is_well_typed(*expression_id, expressions, type_variable_info)
      }
      Expression::StructLiteral(_, vals) => vals
         .values()
         .flatten()
         .all(|x| tree_is_well_typed(*x, expressions, type_variable_info)),
      Expression::Cast {
         cast_type: _,
         target_type,
         expr,
      } => well_typed(target_type, type_variable_info) && tree_is_well_typed(*expr, expressions, type_variable_info),
      Expression::BoundFcnLiteral(_, expression_type_nodes) => expression_type_nodes
         .iter_mut()
         .map(|x| &mut x.e_type)
         .all(|t| well_typed(t, type_variable_info)),
      Expression::IfX(a, b, c) => {
         tree_is_well_typed(*a, expressions, type_variable_info)
            && tree_is_well_typed(*b, expressions, type_variable_info)
            && tree_is_well_typed(*c, expressions, type_variable_info)
      }
      Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedEnumLiteral(_, _)
      | Expression::UnresolvedProcLiteral(_, _) => false,
      Expression::Variable(_)
      | Expression::EnumLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral => true,
   };
   expressions[expr_id].expression = the_expr;
   children_ok && well_typed(expressions[expr_id].exp_type.as_mut().unwrap(), type_variable_info)
}
