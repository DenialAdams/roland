use super::ValidationContext;
use crate::parse::{Expression, ExpressionId};
use crate::type_data::{ExpressionType, ValueType};

// Returns false if the types being inferred are incompatible
// Inference may still not be possible for other reasons
fn inference_is_possible(current_type: &ExpressionType, potential_type: &ExpressionType) -> bool {
   match current_type {
      ExpressionType::Value(ValueType::Array(src_e, _)) => match potential_type {
         ExpressionType::Value(ValueType::Array(target_e, _)) => inference_is_possible(src_e, target_e),
         _ => false,
      },
      ExpressionType::Value(ValueType::UnknownFloat(_)) => potential_type.is_known_or_unknown_float(),
      ExpressionType::Value(ValueType::UnknownInt(_)) => potential_type.is_known_or_unknown_int(),
      ExpressionType::Pointer(src_indirection, ValueType::UnknownFloat(_)) => match potential_type {
         ExpressionType::Pointer(target_indirection, ValueType::UnknownFloat(_)) => {
            src_indirection == target_indirection
         }
         ExpressionType::Pointer(target_indirection, ValueType::Float(_)) => src_indirection == target_indirection,
         _ => false,
      },
      ExpressionType::Pointer(src_indirection, ValueType::UnknownInt(_)) => match potential_type {
         ExpressionType::Pointer(target_indirection, ValueType::UnknownInt(_)) => src_indirection == target_indirection,
         ExpressionType::Pointer(target_indirection, ValueType::Int(_)) => src_indirection == target_indirection,
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
   let current_type = validation_context.expressions[expr_index].exp_type.as_ref().unwrap();
   if !inference_is_possible(current_type, e_type) {
      return;
   }

   set_inferred_type(e_type, expr_index, validation_context);
}

fn set_inferred_type(e_type: &ExpressionType, expr_index: ExpressionId, validation_context: &mut ValidationContext) {
   debug_assert!(inference_is_possible(validation_context.expressions[expr_index].exp_type.as_ref().unwrap(), e_type));

   // SAFETY: it's paramount that this pointer stays valid, so we can't let the expression array resize
   // while this pointer is alive. We don't do this, because we update this expression in place.
   let inferring_expr = std::ptr::addr_of_mut!(validation_context.expressions[expr_index]);

   match unsafe { &(*inferring_expr).expression } {
      Expression::BoundFcnLiteral(_, _) => unreachable!(),
      Expression::Cast { .. } => unreachable!(),
      Expression::BoolLiteral(_) => unreachable!(),
      Expression::IntLiteral { .. } => {
         if let ExpressionType::Value(ValueType::UnknownInt(e_tv)) = e_type {
            let my_tv = match validation_context.expressions[expr_index].exp_type.as_ref().unwrap() {
               ExpressionType::Value(ValueType::UnknownInt(x)) => *x,
               _ => unreachable!(),
            };
            validation_context.type_variables.union(my_tv, *e_tv);
         } else {
            validation_context.unknown_ints.remove(&expr_index);
         }
         *validation_context.expressions[expr_index].exp_type.as_mut().unwrap() = e_type.clone();
      }
      Expression::FloatLiteral(_) => {
         if let ExpressionType::Value(ValueType::UnknownFloat(e_tv)) = e_type {
            let my_tv = match validation_context.expressions[expr_index].exp_type.as_ref().unwrap() {
               ExpressionType::Value(ValueType::UnknownFloat(x)) => *x,
               _ => unreachable!(),
            };
            validation_context.type_variables.union(my_tv, *e_tv);
         } else {
            validation_context.unknown_floats.remove(&expr_index);
         }
         *validation_context.expressions[expr_index].exp_type.as_mut().unwrap() = e_type.clone();
      }
      Expression::StringLiteral(_) => unreachable!(),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         set_inferred_type(e_type, *lhs, validation_context);
         set_inferred_type(e_type, *rhs, validation_context);
         *validation_context.expressions[expr_index].exp_type.as_mut().unwrap() = e_type.clone();
      }
      Expression::UnaryOperator(unop, e) => {
         match unop {
            crate::parse::UnOp::Negate |
            crate::parse::UnOp::Complement => set_inferred_type(e_type, *e, validation_context),
            crate::parse::UnOp::AddressOf => {
               // reverse the indirection
               let mut reversed = e_type.clone();
               reversed.decrement_indirection_count().unwrap();
               set_inferred_type(&reversed, *e, validation_context);
            },
            crate::parse::UnOp::Dereference => {
               let mut reversed = e_type.clone();
               reversed.increment_indirection_count();
               set_inferred_type(&reversed, *e, validation_context);
            },
        }
         *validation_context.expressions[expr_index].exp_type.as_mut().unwrap() = e_type.clone();
      }
      Expression::UnitLiteral => unreachable!(),
      Expression::Variable(_) => {
         // Variable could have any of the following types:
         // - an unknown type directly
         // - a pointer to an unkown type
         // - an array of an unkown type
         // (and recursive variants: an array of arrays of pointers to an unknown type...)
         // We must take care to preserve the existing type structure.

        // dbg!(validation_context.expressions[expr_index].exp_type.as_ref().unwrap(), e_type);
         let (my_tv, incoming_definition) = get_type_variable_of_unknown_type_and_associated_e_type(
            validation_context.expressions[expr_index].exp_type.as_ref().unwrap(),
            e_type,
         )
         .unwrap();

         let outer_representative = validation_context.type_variables.find(my_tv);

         if e_type.is_concrete() {
            // Update existing variables immediately, so that future uses can't change the inferred type
            // (Is this a performance problem? It's obviously awkward, but straightforward)
            for var_in_scope in validation_context.variable_types.values_mut() {
               let Some(inner_tv) = var_in_scope.var_type.get_type_variable_of_unknown_type() else {
                  continue;
               };

               let representative = validation_context.type_variables.find(inner_tv);

               if representative == outer_representative {
                  *get_unknown_portion_of_type(&mut var_in_scope.var_type).unwrap() = incoming_definition.clone();
               }
            }

            validation_context
               .type_variable_definitions
               .insert(outer_representative, incoming_definition);
         } else {
            validation_context
               .type_variables
               .union(my_tv, e_type.get_type_variable_of_unknown_type().unwrap());
         }

         *validation_context.expressions[expr_index].exp_type.as_mut().unwrap() = e_type.clone();
      }
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::ProcedureCall { .. } => unreachable!(),
      Expression::StructLiteral(_, _) => unreachable!(),
      Expression::FieldAccess(_, _) => unreachable!(),
      Expression::ArrayLiteral(exprs) => {
         let ExpressionType::Value(ValueType::Array(target_elem_type, _)) = e_type else { unreachable!() };

         for expr in exprs.iter() {
            set_inferred_type(target_elem_type, *expr, validation_context);
         }

         // It's important that we don't override the length here; that can't be inferred
         match &mut validation_context.expressions[expr_index].exp_type {
            Some(ExpressionType::Value(ValueType::Array(a_type, _))) => *a_type = target_elem_type.clone(),
            _ => unreachable!(),
         }
      }
      Expression::ArrayIndex { array, index: _index } => {
         let ExpressionType::Value(ValueType::Array(_, real_array_len)) = validation_context.expressions[*array].exp_type.as_ref().unwrap() else {
            unreachable!()
         };
         let array_type = ExpressionType::Value(ValueType::Array(Box::new(e_type.clone()), *real_array_len));
         set_inferred_type(&array_type, *array, validation_context);
         *validation_context.expressions[expr_index].exp_type.as_mut().unwrap() = e_type.clone();
      }
      Expression::EnumLiteral(_, _) => unreachable!(),
   }
}

fn get_type_variable_of_unknown_type_and_associated_e_type(
   unknown_type: &ExpressionType,
   type_coming_in: &ExpressionType,
) -> Option<(usize, ValueType)> {
   // Strip down the provided type to get its associated type variable
   match (unknown_type, type_coming_in) {
      (ExpressionType::Value(ValueType::UnknownFloat(x)), ExpressionType::Value(y)) => Some((*x, y.clone())),
      (ExpressionType::Value(ValueType::UnknownInt(x)), ExpressionType::Value(y)) => Some((*x, y.clone())),
      (ExpressionType::Pointer(_, ValueType::UnknownFloat(x)), ExpressionType::Pointer(_, y)) => {
         Some((*x, y.clone()))
      }
      (ExpressionType::Pointer(_, ValueType::UnknownInt(x)), ExpressionType::Pointer(_, y)) => {
         Some((*x, y.clone()))
      }
      (
         ExpressionType::Value(ValueType::Array(unknown_type_inner, _)),
         ExpressionType::Value(ValueType::Array(type_coming_in_inner, _)),
      ) => get_type_variable_of_unknown_type_and_associated_e_type(unknown_type_inner, type_coming_in_inner),
      // other types can't contain unknown values, at least right now
      _ => None,
   }
}

fn get_unknown_portion_of_type(et: &mut ExpressionType) -> Option<&mut ValueType> {
   match et {
      ExpressionType::Value(x @ ValueType::UnknownFloat(_)) => Some(x),
      ExpressionType::Value(x @ ValueType::UnknownInt(_)) => Some(x),
      ExpressionType::Pointer(_, x @ ValueType::UnknownFloat(_)) => Some(x),
      ExpressionType::Pointer(_, x @ ValueType::UnknownInt(_)) => Some(x),
      ExpressionType::Value(ValueType::Array(v, _)) => get_unknown_portion_of_type(v),
      _ => None,
   }
}
