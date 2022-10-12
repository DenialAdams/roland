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
         *validation_context.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap()
            .get_value_type_or_value_being_pointed_to_mut() = e_type.get_value_type_or_value_being_pointed_to().clone();
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
         *validation_context.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap()
            .get_value_type_or_value_being_pointed_to_mut() = e_type.get_value_type_or_value_being_pointed_to().clone();
      }
      Expression::StringLiteral(_) => unreachable!(),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         set_inferred_type(e_type, *lhs, validation_context);
         set_inferred_type(e_type, *rhs, validation_context);
         *validation_context.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap()
            .get_value_type_or_value_being_pointed_to_mut() = e_type.get_value_type_or_value_being_pointed_to().clone();
      }
      Expression::UnaryOperator(_, e) => {
         set_inferred_type(e_type, *e, validation_context);
         *validation_context.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap()
            .get_value_type_or_value_being_pointed_to_mut() = e_type.get_value_type_or_value_being_pointed_to().clone();
      }
      Expression::UnitLiteral => unreachable!(),
      Expression::Variable(_) => {
         let my_tv = match validation_context.expressions[expr_index].exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::UnknownFloat(x)) => *x,
            ExpressionType::Value(ValueType::UnknownInt(x)) => *x,
            ExpressionType::Pointer(_, ValueType::UnknownFloat(x)) => *x,
            ExpressionType::Pointer(_, ValueType::UnknownInt(x)) => *x,
            _ => unreachable!(),
         };

         let outer_representative = validation_context.type_variables.find(my_tv);

         if e_type.is_concrete() {
            let old_value = validation_context
               .type_variable_definitions
               .insert(outer_representative, e_type.clone());
            debug_assert!(old_value.map_or(true, |ov| ov == *e_type));

            // Update existing variables immediately, so that future uses can't change the inferred type
            // (Is this a performance problem? It's obviously awkward, but straightforward)
            for var_in_scope in validation_context.variable_types.values_mut() {
               let inner_tv = match var_in_scope.var_type {
                  ExpressionType::Value(ValueType::UnknownFloat(x)) => x,
                  ExpressionType::Value(ValueType::UnknownInt(x)) => x,
                  ExpressionType::Pointer(_, ValueType::UnknownFloat(x)) => x,
                  ExpressionType::Pointer(_, ValueType::UnknownInt(x)) => x,
                  _ => continue,
               };

               let representative = validation_context.type_variables.find(inner_tv);

               if representative == outer_representative {
                  *var_in_scope.var_type.get_value_type_or_value_being_pointed_to_mut() =
                     e_type.get_value_type_or_value_being_pointed_to().clone();
               }
            }
         } else {
            match e_type {
               ExpressionType::Pointer(_, ValueType::UnknownInt(e_tv) | ValueType::UnknownFloat(e_tv))
               | ExpressionType::Value(ValueType::UnknownInt(e_tv) | ValueType::UnknownFloat(e_tv)) => {
                  validation_context.type_variables.union(my_tv, *e_tv);
               }
               _ => unreachable!(),
            }
         }

         *validation_context.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap()
            .get_value_type_or_value_being_pointed_to_mut() = e_type.get_value_type_or_value_being_pointed_to().clone();
      }
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::ProcedureCall { .. } => unreachable!(),
      Expression::StructLiteral(_, _) => unreachable!(),
      Expression::FieldAccess(_, _) => unreachable!(),
      Expression::ArrayLiteral(exprs) => {
         let target_elem_type = match e_type {
            ExpressionType::Value(ValueType::Array(inner_type, _)) => inner_type,
            _ => unreachable!(),
         };

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
         // The length is bogus, but we don't care about that during inference anyway
         let array_type = ExpressionType::Value(ValueType::Array(Box::new(e_type.clone()), 0));
         set_inferred_type(&array_type, *array, validation_context);
         *validation_context.expressions[expr_index]
            .exp_type
            .as_mut()
            .unwrap()
            .get_value_type_or_value_being_pointed_to_mut() = e_type.get_value_type_or_value_being_pointed_to().clone();
      }
      Expression::EnumLiteral(_, _) => unreachable!(),
   }
}
