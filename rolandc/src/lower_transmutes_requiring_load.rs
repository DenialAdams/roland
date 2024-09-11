use crate::parse::{CastType, Expression, ExpressionId, ExpressionNode, ExpressionPool, UnOp};
use crate::type_data::ExpressionType;

fn is_reinterpretable_transmute(source_type: &ExpressionType, target_type: &ExpressionType) -> bool {
   source_type == target_type
      || matches!(
         (source_type, &target_type),
         (
            ExpressionType::Int(_)
               | ExpressionType::Float(_)
               | ExpressionType::Pointer(_)
               | ExpressionType::Bool
               | ExpressionType::Enum(_)
               | ExpressionType::ProcedurePointer { .. },
            ExpressionType::Int(_)
               | ExpressionType::Float(_)
               | ExpressionType::Pointer(_)
               | ExpressionType::Bool
               | ExpressionType::Enum(_)
               | ExpressionType::ProcedurePointer { .. }
         )
      )
}

pub fn lower(expressions: &mut ExpressionPool) {
   let to_lower: Vec<ExpressionId> = expressions
      .iter()
      .filter(|(_, expr)| match &expr.expression {
         Expression::Cast {
            cast_type: CastType::Transmute,
            target_type,
            expr: child,
         } => !is_reinterpretable_transmute(expressions[*child].exp_type.as_ref().unwrap(), target_type),
         _ => false,
      })
      .map(|(id, _)| id)
      .collect();
   for id_to_lower in to_lower {
      let transmute_location = expressions[id_to_lower].location;
      let (transmute_child, should_remove_transmute) = match &expressions[id_to_lower].expression {
         Expression::Cast { expr: child, .. } => (
            *child,
            expressions[*child].exp_type.as_ref().unwrap() == expressions[id_to_lower].exp_type.as_ref().unwrap(),
         ),
         _ => unreachable!(),
      };

      if should_remove_transmute {
         expressions[id_to_lower].expression =
            std::mem::replace(&mut expressions[transmute_child].expression, Expression::UnitLiteral);
      } else {
         // x transmute T -> (&x transmute &T)~
         let child_type = expressions[transmute_child].exp_type.clone().unwrap();
         let transmute_type = expressions[id_to_lower].exp_type.clone().unwrap();
         let ref_node = expressions.insert(ExpressionNode {
            expression: Expression::UnaryOperator(UnOp::AddressOf, transmute_child),
            location: transmute_location,
            exp_type: Some(ExpressionType::Pointer(Box::new(child_type))),
         });
         let new_transmute = expressions.insert(ExpressionNode {
            expression: Expression::Cast {
               cast_type: CastType::Transmute,
               target_type: transmute_type.clone(),
               expr: ref_node,
            },
            location: transmute_location,
            exp_type: Some(ExpressionType::Pointer(Box::new(transmute_type))),
         });
         expressions[id_to_lower].expression = Expression::UnaryOperator(UnOp::Dereference, new_transmute);
      }
   }
}
