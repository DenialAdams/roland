use crate::Program;
use crate::parse::{BinOp, Expression, ExpressionId, ExpressionNode, all_expression_pools_mut};
use crate::type_data::ExpressionType;

pub fn lower_logical_ops(program: &mut Program) {
   let mut logical_ops: Vec<ExpressionId> = vec![];
   for ast in all_expression_pools_mut(&mut program.global_exprs, &mut program.procedure_bodies) {
      for (expression, v) in ast.iter() {
         let Expression::BinaryOperator {
            operator: BinOp::LogicalAnd | BinOp::LogicalOr,
            ..
         } = &v.expression
         else {
            continue;
         };
         logical_ops.push(expression);
      }
      for id in logical_ops.drain(..) {
         let location = ast[id].location;
         let (operator, lhs, rhs) = {
            let Expression::BinaryOperator { operator, lhs, rhs } = &ast[id].expression else {
               continue;
            };
            (*operator, *lhs, *rhs)
         };

         let (then_br, else_br) = match operator {
            BinOp::LogicalAnd => (
               rhs,
               ast.insert(ExpressionNode {
                  expression: Expression::BoolLiteral(false),
                  exp_type: Some(ExpressionType::Bool),
                  location,
               }),
            ),
            BinOp::LogicalOr => (
               ast.insert(ExpressionNode {
                  expression: Expression::BoolLiteral(true),
                  exp_type: Some(ExpressionType::Bool),
                  location,
               }),
               rhs,
            ),
            _ => unreachable!(),
         };

         // a and b
         //  =>
         // if a { b } else { false }

         // a or b
         //  =>
         // if a { true } else { b }

         ast[id].expression = Expression::IfX(lhs, then_br, else_br);
      }
   }
}
