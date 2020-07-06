use crate::parse::{ExpressionNode, Expression, ExpressionType, Program, Statement, UnOp, BinOp};

pub fn type_and_check_validity(program: &mut Program) {
   for procedure in program.procedures.iter_mut() {
      for statement in procedure.block.statements.iter_mut() {
         match statement {
            Statement::ExpressionStatement(en) => do_type(en),
            _ => (),
         }
      }
   }
}

fn do_type(expr_node: &mut ExpressionNode) {
   match &mut expr_node.expression {
      Expression::IntLiteral(_) => {
         expr_node.exp_type = Some(ExpressionType::Int);
      }
      Expression::StringLiteral(_) => {
         expr_node.exp_type = Some(ExpressionType::String);
      }
      Expression::BinaryOperator(bin_op, e) => {
         do_type(&mut e.0);
         do_type(&mut e.1);

         let correct_arg_types: &[ExpressionType] = match bin_op {
            BinOp::Add | BinOp::Subtract | BinOp::Multiply | BinOp::Divide | BinOp::GreaterThan | BinOp::GreaterThanOrEqualTo | BinOp::LessThan | BinOp::LessThanOrEqualTo => &[ExpressionType::Int],
            BinOp::Equality | BinOp::NotEquality => &[ExpressionType::Int, ExpressionType::Bool],
         };

         if !correct_arg_types.contains(e.0.exp_type.as_ref().unwrap()) {
            eprintln!("Binary operator {:?} requires LHS to have type matching {:?}; instead got {:?}", bin_op, correct_arg_types, e.0.exp_type.as_ref().unwrap());
            unimplemented!()
         }

         if !correct_arg_types.contains(e.1.exp_type.as_ref().unwrap()) {
            eprintln!("Binary operator {:?} requires LHS to have type matching {:?}; instead got {:?}", bin_op, correct_arg_types, e.1.exp_type.as_ref().unwrap());
            unimplemented!()
         }

         if e.0.exp_type != e.1.exp_type {
            eprintln!("Binary operator {:?} requires LHS and RHS to have identical type; instead got {:?} and {:?}", bin_op, e.0.exp_type.as_ref().unwrap(), e.1.exp_type.as_ref().unwrap());
            unimplemented!()
         }

         let result_type = match bin_op {
            BinOp::Add | BinOp::Subtract | BinOp::Multiply | BinOp::Divide => ExpressionType::Int,
            BinOp::Equality | BinOp::NotEquality | BinOp::GreaterThan | BinOp::GreaterThanOrEqualTo | BinOp::LessThan | BinOp::LessThanOrEqualTo => ExpressionType::Bool,
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::UnaryOperator(un_op, e) => {
         do_type(e);
         let correct_type = match un_op {
            UnOp::Negate => ExpressionType::Int,
            UnOp::LogicalNegate => ExpressionType::Bool,
         };
         if e.exp_type.as_ref().unwrap() != &correct_type {
            eprintln!("Expected type {:?} for expression {:?}; instead got {:?}", correct_type, un_op, e.exp_type.as_ref().unwrap());
            unimplemented!()
         }
         expr_node.exp_type = Some(correct_type);
      }
      Expression::Variable(_) => {
         unimplemented!()
      }
      Expression::ProcedureCall(_, _) => {
         expr_node.exp_type = Some(ExpressionType::Unit);
      }
   }
}
