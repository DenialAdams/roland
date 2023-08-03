use crate::parse::{BinOp, Expression, ExpressionId, ExpressionNode};
use crate::type_data::ExpressionType;
use crate::Program;

pub fn lower_logical_ops(program: &mut Program) {
   let mut logical_ops: Vec<ExpressionId> = vec![];
   for (expression, v) in program.ast.expressions.iter() {
      let Expression::BinaryOperator {
         operator: BinOp::LogicalAnd | BinOp::LogicalOr,
         ..
      } = &v.expression
      else {
         continue;
      };
      logical_ops.push(expression);
   }
   for id in logical_ops {
      let location = program.ast.expressions[id].location;
      let (operator, lhs, rhs) = {
         let Expression::BinaryOperator { operator, lhs, rhs } = &program.ast.expressions[id].expression else {
            continue;
         };
         (*operator, *lhs, *rhs)
      };

      let (then_br, else_br) = match operator {
         BinOp::LogicalAnd => (
            rhs,
            program.ast.expressions.insert(ExpressionNode {
               expression: Expression::BoolLiteral(false),
               exp_type: Some(ExpressionType::Bool),
               location,
            }),
         ),
         BinOp::LogicalOr => (
            program.ast.expressions.insert(ExpressionNode {
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

      program.ast.expressions[id].expression = Expression::IfX(lhs, then_br, else_br);
   }
}
