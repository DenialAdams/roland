use std::borrow::Cow;

use slotmap::SecondaryMap;

use super::type_variables::{TypeConstraint, TypeVariable, TypeVariableManager};
use super::OwnedValidationContext;
use crate::error_handling::error_handling_macros::rolandc_error_w_details;
use crate::error_handling::ErrorManager;
use crate::parse::{Expression, ExpressionId, ExpressionPool, ProcedureBody, ProcedureId};
use crate::type_data::{ExpressionType, IntType};

fn unknowns_are_compatible(x: TypeVariable, y: TypeVariable, type_variables: &TypeVariableManager) -> bool {
   let x_data = type_variables.get_data(x);
   let y_data = type_variables.get_data(y);

   match (x_data.constraint, y_data.constraint) {
      (x, y) if x == y => true,
      (TypeConstraint::None, _)
      | (_, TypeConstraint::None)
      | (TypeConstraint::Int, TypeConstraint::SignedInt)
      | (TypeConstraint::SignedInt, TypeConstraint::Int) => true,
      _ => false,
   }
}

fn meet(current_type: &ExpressionType, incoming_type: &ExpressionType, type_variables: &mut TypeVariableManager) {
   match (current_type, incoming_type) {
      (ExpressionType::Array(current_base, _), ExpressionType::Array(incoming_base, _))
      | (ExpressionType::Pointer(current_base), ExpressionType::Pointer(incoming_base)) => {
         meet(current_base, incoming_base, type_variables);
      }
      (ExpressionType::Struct(_, current_type_arguments), ExpressionType::Struct(_, incoming_type_arguments))
      | (ExpressionType::Union(_, current_type_arguments), ExpressionType::Union(_, incoming_type_arguments)) => {
         for (x, y) in current_type_arguments.iter().zip(incoming_type_arguments) {
            meet(x, y, type_variables);
         }
      }
      (ExpressionType::Unknown(current_tv), ExpressionType::Unknown(incoming_tv)) => {
         debug_assert!(unknowns_are_compatible(*current_tv, *incoming_tv, type_variables));
         type_variables.union(*current_tv, *incoming_tv);
      }
      (ExpressionType::Unknown(current_tv), _) => {
         debug_assert!(type_variables
            .get_data(*current_tv)
            .known_type
            .as_ref()
            .map_or(true, |x| x == incoming_type));
         type_variables
            .get_data_mut(*current_tv)
            .known_type
            .get_or_insert_with(|| incoming_type.clone());
      }
      _ => unreachable!(),
   }
}

fn inference_is_possible(
   current_type: &ExpressionType,
   potential_type: &ExpressionType,
   type_variables: &TypeVariableManager,
) -> bool {
   match (current_type, potential_type) {
      (ExpressionType::Array(current_base, _), ExpressionType::Array(potential_base, _))
      | (ExpressionType::Pointer(current_base), ExpressionType::Pointer(potential_base)) => {
         inference_is_possible(current_base, potential_base, type_variables)
      }
      (ExpressionType::Unknown(x), _) => {
         let data = type_variables.get_data(*x);

         if data.known_type.is_some() {
            return false;
         }

         if let ExpressionType::Unknown(y) = potential_type {
            return unknowns_are_compatible(*x, *y, type_variables);
         }

         match data.constraint {
            TypeConstraint::None => true,
            TypeConstraint::Float => matches!(potential_type, ExpressionType::Float(_)),
            TypeConstraint::SignedInt => matches!(potential_type, ExpressionType::Int(IntType { signed: true, .. })),
            TypeConstraint::Int => matches!(potential_type, ExpressionType::Int(_)),
         }
      }
      (
         ExpressionType::Struct(base_id, current_type_arguments),
         ExpressionType::Struct(potential_base_id, potential_type_arguments),
      ) => {
         if base_id != potential_base_id
            || current_type_arguments.len() == 0
            || current_type_arguments.len() != potential_type_arguments.len()
         {
            return false;
         }
         // It may be that after inferring one type parameter, inference is no longer possible as a whole
         // I claim this is OK as long as we are doing inference one step at a time
         current_type_arguments
            .iter()
            .zip(potential_type_arguments.iter())
            .all(|(x, y)| inference_is_possible(x, y, type_variables))
      }
      (
         ExpressionType::Union(base_id, current_type_arguments),
         ExpressionType::Union(potential_base_id, potential_type_arguments),
      ) => {
         if base_id != potential_base_id
            || current_type_arguments.len() == 0
            || current_type_arguments.len() != potential_type_arguments.len()
         {
            return false;
         }
         // It may be that after inferring one type parameter, inference is no longer possible as a whole
         // I claim this is OK as long as we are doing inference one step at a time
         current_type_arguments
            .iter()
            .zip(potential_type_arguments.iter())
            .all(|(x, y)| inference_is_possible(x, y, type_variables))
      }
      _ => false,
   }
}

pub fn try_merge_types(
   e_type: &ExpressionType,
   current_type: &mut Cow<ExpressionType>,
   type_variables: &mut TypeVariableManager,
) {
   if !inference_is_possible(current_type, e_type, type_variables) {
      return;
   }

   let current_type = current_type.to_mut();
   meet(current_type, e_type, type_variables);
   *current_type = e_type.clone();
}

pub fn try_set_inferred_type(
   e_type: &ExpressionType,
   expr_index: ExpressionId,
   validation_context: &mut OwnedValidationContext,
   expressions: &mut ExpressionPool,
) {
   let current_type = expressions[expr_index].exp_type.as_ref().unwrap();
   if !inference_is_possible(current_type, e_type, &validation_context.type_variables) {
      return;
   }

   set_inferred_type(e_type, expr_index, validation_context, expressions);
}

fn set_inferred_type(
   e_type: &ExpressionType,
   expr_index: ExpressionId,
   validation_context: &mut OwnedValidationContext,
   expressions: &mut ExpressionPool,
) {
   let the_expr = std::mem::replace(&mut expressions[expr_index].expression, Expression::UnitLiteral);
   match &the_expr {
      Expression::IntLiteral { .. } | Expression::FloatLiteral(_) => {
         meet(
            expressions[expr_index].exp_type.as_ref().unwrap(),
            e_type,
            &mut validation_context.type_variables,
         );
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         set_inferred_type(e_type, *lhs, validation_context, expressions);
         set_inferred_type(e_type, *rhs, validation_context, expressions);
      }
      Expression::IfX(_, b, c) => {
         try_set_inferred_type(e_type, *b, validation_context, expressions);
         try_set_inferred_type(e_type, *c, validation_context, expressions);
      }
      Expression::UnaryOperator(unop, e) => {
         match unop {
            crate::parse::UnOp::Negate | crate::parse::UnOp::Complement => {
               set_inferred_type(e_type, *e, validation_context, expressions);
            }
            crate::parse::UnOp::AddressOf => {
               // reverse the indirection
               match e_type {
                  ExpressionType::Pointer(inner) => {
                     set_inferred_type(inner, *e, validation_context, expressions);
                  }
                  _ => unreachable!(),
               }
            }
            crate::parse::UnOp::Dereference => {
               let reversed = ExpressionType::Pointer(Box::new(e_type.clone()));
               set_inferred_type(&reversed, *e, validation_context, expressions);
            }
         }
      }
      Expression::Variable(_) => {
         // Variable could have any of the following types:
         // - an unknown type directly
         // - a pointer to an unknown type
         // - an array of an unknown type
         // (and recursive variants: an array of arrays of pointers to an unknown type...)
         // We must take care to preserve the existing type structure.

         meet(
            expressions[expr_index].exp_type.as_ref().unwrap(),
            e_type,
            &mut validation_context.type_variables,
         );

         // Update existing variables immediately, so that error messages have good types
         // (this should _not_ affect correctness.)
         for var_in_scope in validation_context.variable_types.values_mut() {
            lower_unknowns_in_type(&mut var_in_scope.var_type, &validation_context.type_variables);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         let ExpressionType::Array(target_elem_type, _) = e_type else {
            unreachable!()
         };

         for expr in exprs.iter() {
            set_inferred_type(target_elem_type, *expr, validation_context, expressions);
         }

         // I can not come up with a scenario where this meet matters, but not doing it seems wrong.
         meet(
            expressions[expr_index].exp_type.as_ref().unwrap(),
            e_type,
            &mut validation_context.type_variables,
         );
      }
      Expression::ArrayIndex { array, index: _index } => {
         let ExpressionType::Array(_, real_array_len) = expressions[*array].exp_type.as_ref().unwrap() else {
            unreachable!()
         };
         let array_type = ExpressionType::Array(Box::new(e_type.clone()), *real_array_len);
         try_set_inferred_type(&array_type, *array, validation_context, expressions);
      }
      Expression::ProcedureCall { .. } => {
         meet(
            expressions[expr_index].exp_type.as_ref().unwrap(),
            e_type,
            &mut validation_context.type_variables,
         );
      }
      Expression::StringLiteral(_)
      | Expression::EnumLiteral(_, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::StructLiteral(_, _)
      | Expression::FieldAccess(_, _)
      | Expression::UnitLiteral
      | Expression::BoundFcnLiteral(_, _)
      | Expression::Cast { .. }
      | Expression::BoolLiteral(_)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
   expressions[expr_index].expression = the_expr;
   *expressions[expr_index].exp_type.as_mut().unwrap() = e_type.clone();
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
