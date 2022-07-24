use super::ValidationContext;
use crate::error_handling::ErrorManager;
use crate::interner::Interner;
use crate::parse::{Expression, ExpressionId};
use crate::type_data::{ExpressionType, ValueType};

// Returns false if the types being inferred are incompatible
// Inference may still not be possible for other reasons
fn inference_is_impossible(current_type: &ExpressionType, potential_type: &ExpressionType) -> bool {
   match current_type {
      ExpressionType::Value(ValueType::Array(src_e, _)) => match potential_type {
         ExpressionType::Value(ValueType::Array(target_e, _)) => inference_is_impossible(src_e, target_e),
         _ => true,
      },
      ExpressionType::Value(ValueType::UnknownFloat(_)) => !potential_type.is_known_or_unknown_float(),
      ExpressionType::Value(ValueType::UnknownInt(_)) => !potential_type.is_known_or_unknown_int(),
      _ => true,
   }
}

pub fn try_set_inferred_type(
   e_type: &ExpressionType,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
) {
   let current_type = validation_context.expressions[expr_index].exp_type.as_ref().unwrap();
   if inference_is_impossible(current_type, e_type) {
      return;
   }

   set_inferred_type(e_type, expr_index, validation_context, err_manager, interner);
}

fn set_inferred_type(
   e_type: &ExpressionType,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
) {
   // this clone is very sad, but we do it for borrowck
   let expr = validation_context.expressions[expr_index].expression.clone();
   match &expr {
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
         validation_context.expressions[expr_index].exp_type = Some(e_type.clone());
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
         validation_context.expressions[expr_index].exp_type = Some(e_type.clone());
      }
      Expression::StringLiteral(_) => unreachable!(),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         set_inferred_type(e_type, *lhs, validation_context, err_manager, interner);
         set_inferred_type(e_type, *rhs, validation_context, err_manager, interner);
         validation_context.expressions[expr_index].exp_type = Some(e_type.clone());
      }
      Expression::UnaryOperator(_, e) => {
         set_inferred_type(e_type, *e, validation_context, err_manager, interner);
         validation_context.expressions[expr_index].exp_type = Some(e_type.clone());
      }
      Expression::UnitLiteral => unreachable!(),
      Expression::Variable(_) => {
         let my_tv = match validation_context.expressions[expr_index].exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::UnknownFloat(x)) => *x,
            ExpressionType::Value(ValueType::UnknownInt(x)) => *x,
            _ => unreachable!(),
         };

         let outer_representative = validation_context.type_variables.find(my_tv);

         debug_assert!(!validation_context
            .type_variable_definitions
            .contains_key(&outer_representative));

         if e_type.is_concrete_type() {
            validation_context
               .type_variable_definitions
               .insert(outer_representative, e_type.clone());

            // Update existing variables immediately, so that future uses can't change the inferred type
            // (Is this a performance problem? It's obviously awkward, but straight forward)
            for var_in_scope in validation_context.variable_types.values_mut() {
               let my_tv = match var_in_scope.var_type {
                  ExpressionType::Value(ValueType::UnknownFloat(x)) => x,
                  ExpressionType::Value(ValueType::UnknownInt(x)) => x,
                  _ => continue,
               };

               let representative = validation_context.type_variables.find(my_tv);

               if representative == outer_representative {
                  var_in_scope.var_type = e_type.clone();
               }
            }
         } else {
            match e_type {
               ExpressionType::Value(ValueType::UnknownInt(e_tv) | ValueType::UnknownFloat(e_tv)) => {
                  validation_context.type_variables.union(my_tv, *e_tv);
               }
               _ => unreachable!(),
            }
         }

         validation_context.expressions[expr_index].exp_type = Some(e_type.clone());
      }
      Expression::ProcedureCall { .. } => unreachable!(),
      Expression::StructLiteral(_, _) => unreachable!(),
      Expression::FieldAccess(_, _) => unreachable!(),
      Expression::ArrayLiteral(exprs) => {
         let target_elem_type = match e_type {
            ExpressionType::Value(ValueType::Array(inner_type, _)) => inner_type,
            _ => unreachable!(),
         };

         for expr in exprs.iter() {
            set_inferred_type(target_elem_type, *expr, validation_context, err_manager, interner);
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
         set_inferred_type(&array_type, *array, validation_context, err_manager, interner);
         validation_context.expressions[expr_index].exp_type = Some(e_type.clone());
      }
      Expression::EnumLiteral(_, _) => unreachable!(),
   }
}
