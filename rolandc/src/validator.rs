use crate::parse::{BinOp, Expression, ExpressionNode, ExpressionType, Program, Statement, UnOp};
use std::collections::HashMap;

struct ValidationContext {
   error_count: u64,
   variable_types: HashMap<String, ExpressionType>,
}

pub fn type_and_check_validity(program: &mut Program) -> u64 {
   let mut validation_context = ValidationContext {
      error_count: 0,
      variable_types: HashMap::new(),
   };

   for procedure in program.procedures.iter_mut() {
      validation_context.variable_types.clear();

      for statement in procedure.block.statements.iter_mut() {
         match statement {
            Statement::VariableDeclaration(id, en) => {
               do_type(en, &mut validation_context);
               validation_context.variable_types.insert(id.clone(), en.exp_type.clone().unwrap());
            }
            Statement::ExpressionStatement(en) => {
               do_type(en, &mut validation_context);
            }
         }
      }
   }

   validation_context.error_count
}

fn do_type(expr_node: &mut ExpressionNode, validation_context: &mut ValidationContext) {
   match &mut expr_node.expression {
      Expression::IntLiteral(_) => {
         expr_node.exp_type = Some(ExpressionType::Int);
      }
      Expression::StringLiteral(_) => {
         expr_node.exp_type = Some(ExpressionType::String);
      }
      Expression::BinaryOperator(bin_op, e) => {
         do_type(&mut e.0, validation_context);
         do_type(&mut e.1, validation_context);

         let correct_arg_types: &[ExpressionType] = match bin_op {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::GreaterThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThan
            | BinOp::LessThanOrEqualTo => &[ExpressionType::Int],
            BinOp::Equality | BinOp::NotEquality => &[ExpressionType::Int, ExpressionType::Bool],
         };

         let lhs_type = e.0.exp_type.as_ref().unwrap();
         let rhs_type = e.1.exp_type.as_ref().unwrap();

         let result_type = if lhs_type == &ExpressionType::CompileError || rhs_type == &ExpressionType::CompileError {
            // Avoid cascading errors
            ExpressionType::CompileError
         } else if !correct_arg_types.contains(lhs_type) {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {:?}",
               bin_op,
               correct_arg_types,
               e.0.exp_type.as_ref().unwrap()
            );
            ExpressionType::CompileError
         } else if !correct_arg_types.contains(rhs_type) {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {:?}",
               bin_op,
               correct_arg_types,
               e.1.exp_type.as_ref().unwrap()
            );
            ExpressionType::CompileError
         } else if lhs_type != rhs_type {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS and RHS to have identical type; instead got {:?} and {:?}",
               bin_op,
               e.0.exp_type.as_ref().unwrap(),
               e.1.exp_type.as_ref().unwrap()
            );
            ExpressionType::CompileError
         } else {
            match bin_op {
               BinOp::Add | BinOp::Subtract | BinOp::Multiply | BinOp::Divide => ExpressionType::Int,
               BinOp::Equality
               | BinOp::NotEquality
               | BinOp::GreaterThan
               | BinOp::GreaterThanOrEqualTo
               | BinOp::LessThan
               | BinOp::LessThanOrEqualTo => ExpressionType::Bool,
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::UnaryOperator(un_op, e) => {
         do_type(e, validation_context);

         let correct_type = match un_op {
            UnOp::Negate => ExpressionType::Int,
            UnOp::LogicalNegate => ExpressionType::Bool,
         };

         let result_type = if e.exp_type.as_ref().unwrap() == &ExpressionType::CompileError {
            // Avoid cascading errors
            ExpressionType::CompileError
         } else if e.exp_type.as_ref().unwrap() != &correct_type {
            validation_context.error_count += 1;
            eprintln!(
               "Expected type {:?} for expression {:?}; instead got {:?}",
               correct_type,
               un_op,
               e.exp_type.as_ref().unwrap()
            );
            ExpressionType::CompileError
         } else {
            correct_type
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::Variable(id) => {
         let defined_type = validation_context.variable_types.get(id);

         let result_type = match defined_type {
            Some(t) => {
               t.clone()
            },
            None => {
               validation_context.error_count += 1;
               eprintln!(
                  "Encountered undefined variable {}",
                  id
               );
               ExpressionType::CompileError
            }
         };

         expr_node.exp_type = Some(result_type);
      },
      Expression::ProcedureCall(_, args) => {
         for arg in args {
            do_type(arg, validation_context);
         }
         expr_node.exp_type = Some(ExpressionType::Unit);
      }
   }
}
