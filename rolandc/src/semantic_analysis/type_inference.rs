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
         },
         ExpressionType::ProcedurePointer {
            parameters: incoming_parameters,
            ret_type: incoming_ret_type,
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
      ExpressionType::ProcedurePointer { parameters, ret_type } => {
         for p in parameters {
            lower_unknowns_in_type(p, type_variables);
         }
         lower_unknowns_in_type(ret_type, type_variables);
      }
      _ => (),
   }
}
