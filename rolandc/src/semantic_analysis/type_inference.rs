use slotmap::SecondaryMap;

use super::type_variables::{TypeConstraint, TypeVariableManager};
use super::OwnedValidationContext;
use crate::error_handling::error_handling_macros::rolandc_error_w_details;
use crate::error_handling::ErrorManager;
use crate::parse::{Expression, ExpressionPool, ProcedureBody, ProcedureId};
use crate::type_data::{ExpressionType, IntType};

fn constraints_are_compatible(x: TypeConstraint, y: TypeConstraint) -> bool {
   match (x, y) {
      (TypeConstraint::None, _)
      | (_, TypeConstraint::None)
      | (TypeConstraint::Int, TypeConstraint::SignedInt)
      | (TypeConstraint::SignedInt, TypeConstraint::Int) => true,
      _ => x == y,
   }
}

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

fn meet(
   mut current_type: &mut ExpressionType,
   incoming_type: &ExpressionType,
   type_variables: &mut TypeVariableManager,
) {
   match (&mut current_type, incoming_type) {
      (ExpressionType::Array(current_base, current_len), ExpressionType::Array(incoming_base, incoming_len)) => {
         if current_len != incoming_len {
            return;
         }
         meet(current_base, incoming_base, type_variables);
      }
      (ExpressionType::Pointer(current_base), ExpressionType::Pointer(incoming_base)) => {
         meet(current_base, incoming_base, type_variables);
      }
      (
         ExpressionType::Struct(current_base, current_type_arguments),
         ExpressionType::Struct(incoming_base, incoming_type_arguments),
      ) => {
         if current_base != incoming_base {
            return;
         }
         for (x, y) in current_type_arguments.iter_mut().zip(incoming_type_arguments) {
            meet(x, y, type_variables);
         }
      }
      (
         ExpressionType::Union(current_base, current_type_arguments),
         ExpressionType::Union(incoming_base, incoming_type_arguments),
      ) => {
         if current_base != incoming_base {
            return;
         }
         for (x, y) in current_type_arguments.iter_mut().zip(incoming_type_arguments) {
            meet(x, y, type_variables);
         }
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
            return;
         }
         for (x, y) in current_parameters.iter_mut().zip(incoming_parameters) {
            meet(x, y, type_variables);
         }
         meet(current_ret_type, incoming_ret_type, type_variables);
      }
      (ExpressionType::Unknown(current_tv), ExpressionType::Unknown(incoming_tv)) => {
         let current_data = type_variables.get_data(*current_tv);
         if current_data.known_type.is_some() {
            return;
         }
         let incoming_data = type_variables.get_data(*incoming_tv);
         if !constraints_are_compatible(current_data.constraint, incoming_data.constraint) {
            return;
         }
         type_variables.union(*current_tv, *incoming_tv);
         *current_tv = *incoming_tv;
      }
      (ExpressionType::Unknown(current_tv), incoming_type) => {
         let data = type_variables.get_data_mut(*current_tv);
         if data.known_type.is_some() {
            return;
         }
         if !constraint_compatible_with_concrete(data.constraint, incoming_type) {
            return;
         }
         data.known_type = Some(incoming_type.clone());
         *current_type = incoming_type.clone();
      }
      _ => (),
   }
}

// TODO: shouldn't need to clone at many callsites
pub fn try_merge_types(
   e_type: &ExpressionType,
   current_type: &mut ExpressionType,
   type_variables: &mut TypeVariableManager,
) {
   meet(current_type, e_type, type_variables);
   // This seems questionable.
   // It would be better if type equality simply knew how to look up unknown types?
   lower_unknowns_in_type(current_type, type_variables);
}

pub fn lower_type_variables(
   ctx: &mut OwnedValidationContext,
   procedure_bodies: &mut SecondaryMap<ProcedureId, ProcedureBody>,
   expressions: &mut ExpressionPool,
   err_manager: &mut ErrorManager,
) {
   for (i, e) in expressions.iter_mut() {
      if let Some(exp_type) = e.exp_type.as_mut() {
         lower_unknowns_in_type(exp_type, &ctx.type_variables);
         if exp_type.is_concrete() {
            ctx.unknown_literals.swap_remove(&i);
         }
      }
      if let Expression::BoundFcnLiteral(_, type_arguments) = &mut e.expression {
         for type_arg in type_arguments.iter_mut() {
            lower_unknowns_in_type(&mut type_arg.e_type, &ctx.type_variables);
         }
      }
   }

   if !ctx.unknown_literals.is_empty() {
      let err_details: Vec<_> = ctx
         .unknown_literals
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
         ctx.unknown_literals.len()
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
