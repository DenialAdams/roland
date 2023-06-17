use std::ops::Deref;

use super::type_variables::{TypeConstraint, TypeVariable};
use super::validator::is_type_param_with_trait;
use super::ValidationContext;
use crate::parse::{Expression, ExpressionId};
use crate::type_data::{ExpressionType, IntType};

fn unknowns_are_compatible(x: TypeVariable, y: TypeVariable, validation_context: &ValidationContext) -> bool {
   let x_data = validation_context.type_variables.get_data(x);
   let y_data = validation_context.type_variables.get_data(y);

   match (x_data.constraint, y_data.constraint) {
      (x, y) if x == y => true,
      (TypeConstraint::None, _) => true,
      (_, TypeConstraint::None) => true,
      (TypeConstraint::Int, TypeConstraint::SignedInt) => true,
      (TypeConstraint::SignedInt, TypeConstraint::Int) => true,
      _ => false,
   }
}

fn inference_is_possible(
   current_type: &ExpressionType,
   potential_type: &ExpressionType,
   validation_context: &ValidationContext,
) -> bool {
   match current_type {
      ExpressionType::Array(src_e, _) => match potential_type {
         ExpressionType::Array(target_e, _) => inference_is_possible(src_e, target_e, validation_context),
         _ => false,
      },
      ExpressionType::Unknown(x) => {
         let data = validation_context.type_variables.get_data(*x);

         if data.known_type.is_some() {
            return false;
         }

         if let ExpressionType::Unknown(y) = potential_type {
            return unknowns_are_compatible(*x, *y, validation_context);
         }

         match data.constraint {
            TypeConstraint::None => true,
            TypeConstraint::Float => {
               matches!(potential_type, ExpressionType::Float(_))
                  || is_type_param_with_trait(validation_context, potential_type, "Float")
            }
            TypeConstraint::SignedInt => matches!(potential_type, ExpressionType::Int(IntType { signed: true, .. })),
            TypeConstraint::Int => matches!(potential_type, ExpressionType::Int(_)),
         }
      }
      ExpressionType::Pointer(src_e) => match potential_type {
         ExpressionType::Pointer(target_e) => inference_is_possible(src_e, target_e, validation_context),
         _ => false,
      },
      _ => false,
   }
}

pub fn try_set_inferred_type(
   e_type: &ExpressionType,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
) {
   let current_type = validation_context.ast.expressions[expr_index]
      .exp_type
      .as_ref()
      .unwrap();
   if !inference_is_possible(current_type, e_type, validation_context) {
      return;
   }

   set_inferred_type(e_type, expr_index, validation_context);
}

fn set_inferred_type(e_type: &ExpressionType, expr_index: ExpressionId, validation_context: &mut ValidationContext) {
   // TODO: dummy expr?
   let the_expr = std::mem::replace(
      &mut validation_context.ast.expressions[expr_index].expression,
      Expression::UnitLiteral,
   );
   match &the_expr {
      Expression::IntLiteral { .. } | Expression::FloatLiteral(_) => {
         let my_tv = match validation_context.ast.expressions[expr_index]
            .exp_type
            .as_ref()
            .unwrap()
         {
            ExpressionType::Unknown(x) => *x,
            _ => unreachable!(),
         };
         if let ExpressionType::Unknown(e_tv) = e_type {
            debug_assert!(unknowns_are_compatible(my_tv, *e_tv, validation_context));
            validation_context.type_variables.union(my_tv, *e_tv);
         } else {
            debug_assert!(validation_context
               .type_variables
               .get_data(my_tv)
               .known_type
               .as_ref()
               .map_or(true, |x| x == e_type));
            validation_context
               .type_variables
               .get_data_mut(my_tv)
               .known_type
               .get_or_insert_with(|| e_type.clone());
            validation_context.unknown_literals.remove(&expr_index);
         }
         *validation_context.ast.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap() = e_type.clone();
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         set_inferred_type(e_type, *lhs, validation_context);
         set_inferred_type(e_type, *rhs, validation_context);
         *validation_context.ast.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap() = e_type.clone();
      }
      Expression::UnaryOperator(unop, e) => {
         match unop {
            crate::parse::UnOp::Negate | crate::parse::UnOp::Complement => {
               set_inferred_type(e_type, *e, validation_context);
            }
            crate::parse::UnOp::AddressOf => {
               // reverse the indirection
               match e_type {
                  ExpressionType::Pointer(inner) => {
                     set_inferred_type(inner, *e, validation_context);
                  }
                  _ => unreachable!(),
               }
            }
            crate::parse::UnOp::Dereference => {
               let reversed = ExpressionType::Pointer(Box::new(e_type.clone()));
               set_inferred_type(&reversed, *e, validation_context);
            }
         }
         *validation_context.ast.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap() = e_type.clone();
      }
      Expression::Variable(_) => {
         // Variable could have any of the following types:
         // - an unknown type directly
         // - a pointer to an unknown type
         // - an array of an unknown type
         // (and recursive variants: an array of arrays of pointers to an unknown type...)
         // We must take care to preserve the existing type structure.

         let (my_tv, incoming_definition) = get_type_variable_of_unknown_type_and_associated_e_type(
            validation_context.ast.expressions[expr_index]
               .exp_type
               .as_ref()
               .unwrap(),
            e_type,
         )
         .unwrap();

         if let Some(e_tv) = e_type.get_type_variable_of_unknown_type() {
            debug_assert!(unknowns_are_compatible(my_tv, e_tv, validation_context));
            validation_context.type_variables.union(my_tv, e_tv);
         } else {
            let my_tv = validation_context.type_variables.find(my_tv);

            // Update existing variables immediately, so that error messages have good types
            // (this should _not_ affect correctness.)
            // (Is this a performance problem? It's obviously awkward, but straightforward)
            // (The alternative would be to update the type lazily)
            for var_in_scope in validation_context.variable_types.values_mut() {
               let Some(inner_tv) = var_in_scope.var_type.get_type_variable_of_unknown_type() else {
                  continue;
               };

               let representative = validation_context.type_variables.find(inner_tv);

               if representative == my_tv {
                  *var_in_scope.var_type.get_unknown_portion_of_type().unwrap() = incoming_definition.clone();
               }
            }

            debug_assert!(validation_context
               .type_variables
               .get_data(my_tv)
               .known_type
               .as_ref()
               .map_or(true, |x| x == incoming_definition));
            validation_context
               .type_variables
               .get_data_mut(my_tv)
               .known_type
               .get_or_insert_with(|| incoming_definition.clone());
         }

         *validation_context.ast.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap() = e_type.clone();
      }
      Expression::ArrayLiteral(exprs) => {
         let ExpressionType::Array(target_elem_type, _) = e_type else { unreachable!() };

         for expr in exprs.iter() {
            set_inferred_type(target_elem_type, *expr, validation_context);
         }

         // It's important that we don't override the length here; that can't be inferred
         match &mut validation_context.ast.expressions[expr_index].exp_type {
            Some(ExpressionType::Array(a_type, _)) => {
               if target_elem_type.get_type_variable_of_unknown_type().is_none() {
                  let (my_tv, incoming_definition) =
                     get_type_variable_of_unknown_type_and_associated_e_type(a_type, target_elem_type).unwrap();

                  debug_assert!(validation_context
                     .type_variables
                     .get_data(my_tv)
                     .known_type
                     .as_ref()
                     .map_or(true, |x| x == incoming_definition));
                  validation_context
                     .type_variables
                     .get_data_mut(my_tv)
                     .known_type
                     .get_or_insert_with(|| incoming_definition.clone());
                  validation_context.unknown_literals.remove(&expr_index);
               }

               **a_type = target_elem_type.deref().clone();
            }
            _ => unreachable!(),
         }
      }
      Expression::ArrayIndex { array, index: _index } => {
         let ExpressionType::Array(_, real_array_len) = validation_context.ast.expressions[*array].exp_type.as_ref().unwrap() else {
            unreachable!()
         };
         let array_type = ExpressionType::Array(Box::new(e_type.clone()), *real_array_len);
         try_set_inferred_type(&array_type, *array, validation_context);
         *validation_context.ast.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap() = e_type.clone();
      }
      Expression::IfX(_, _, _) => unreachable!(),
      Expression::StringLiteral(_) => unreachable!(),
      Expression::EnumLiteral(_, _) => unreachable!(),
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::ProcedureCall { .. } => unreachable!(),
      Expression::StructLiteral(_, _) => unreachable!(),
      Expression::FieldAccess(_, _) => unreachable!(),
      Expression::UnitLiteral => unreachable!(),
      Expression::BoundFcnLiteral(_, _) => unreachable!(),
      Expression::Cast { .. } => unreachable!(),
      Expression::BoolLiteral(_) => unreachable!(),
   }
   validation_context.ast.expressions[expr_index].expression = the_expr;
}

fn get_type_variable_of_unknown_type_and_associated_e_type<'b>(
   unknown_type: &ExpressionType,
   type_coming_in: &'b ExpressionType,
) -> Option<(TypeVariable, &'b ExpressionType)> {
   // Strip down the provided type to get its associated type variable
   match (unknown_type, type_coming_in) {
      (ExpressionType::Unknown(x), y) => Some((*x, y)),
      (ExpressionType::Array(unknown_type_inner, _), ExpressionType::Array(type_coming_in_inner, _)) => {
         get_type_variable_of_unknown_type_and_associated_e_type(unknown_type_inner, type_coming_in_inner)
      }
      (ExpressionType::Pointer(unknown_type_inner), ExpressionType::Pointer(type_coming_in_inner)) => {
         get_type_variable_of_unknown_type_and_associated_e_type(unknown_type_inner, type_coming_in_inner)
      }
      // other types can't contain unknown values, at least right now
      _ => None,
   }
}
