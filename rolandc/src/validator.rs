use crate::parse::{BinOp, Expression, ExpressionNode, ExpressionType, Program, Statement, UnOp};
use std::collections::{HashMap, HashSet};

struct ProcedureInfo {
   pure: bool,
}

struct ValidationContext {
   string_literals: HashSet<String>,
   procedure_info: HashMap<String, ProcedureInfo>,
   variable_types: HashMap<String, ExpressionType>,
   error_count: u64,
   in_pure_func: bool,
}

pub fn type_and_check_validity(program: &mut Program) -> u64 {
   let mut validation_context = ValidationContext {
      string_literals: HashSet::new(),
      variable_types: HashMap::new(),
      error_count: 0,
      procedure_info: HashMap::new(),
      in_pure_func: false,
   };

   // Standard Library functions
   let standard_lib_procs = [("print", false), ("print_int", false), ("print_bool", false)];
   for p in standard_lib_procs.iter() {
      validation_context
         .procedure_info
         .insert(p.0.to_string(), ProcedureInfo { pure: p.1 });
   }

   for procedure in program.procedures.iter() {
      match validation_context
         .procedure_info
         .insert(procedure.name.clone(), ProcedureInfo { pure: procedure.pure })
      {
         Some(_) => {
            validation_context.error_count += 1;
            eprintln!(
               "Encountered duplicate procedures/functions with the same name `{}`",
               procedure.name
            );
         }
         None => (),
      }
   }

   // We won't proceed with type checking because there could be false positives due to
   // procedure definition errors.
   if validation_context.error_count > 0 {
      return validation_context.error_count;
   }

   for procedure in program.procedures.iter_mut() {
      validation_context.variable_types.clear();
      validation_context.in_pure_func = procedure.pure;

      for statement in procedure.block.statements.iter_mut() {
         match statement {
            Statement::VariableDeclaration(id, en) => {
               do_type(en, &mut validation_context);
               validation_context
                  .variable_types
                  .insert(id.clone(), en.exp_type.clone().unwrap());
            }
            Statement::ExpressionStatement(en) => {
               do_type(en, &mut validation_context);
            }
         }
      }
   }

   program.literals = validation_context.string_literals;

   validation_context.error_count
}

fn do_type(expr_node: &mut ExpressionNode, validation_context: &mut ValidationContext) {
   match &mut expr_node.expression {
      Expression::IntLiteral(_) => {
         expr_node.exp_type = Some(ExpressionType::Int);
      }
      Expression::StringLiteral(lit) => {
         // This clone will become cheap when we intern everywhere
         validation_context.string_literals.insert(lit.clone());
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
            Some(t) => t.clone(),
            None => {
               validation_context.error_count += 1;
               eprintln!("Encountered undefined variable {}", id);
               ExpressionType::CompileError
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::ProcedureCall(name, args) => {
         expr_node.exp_type = Some(ExpressionType::Unit); // Will change when we parse return types

         match validation_context.procedure_info.get(name) {
            Some(procedure_info) => {
               if validation_context.in_pure_func && !procedure_info.pure {
                  validation_context.error_count += 1;
                  eprintln!("Encountered call to procedure `{}` (impure) in func (pure)", name);
                  expr_node.exp_type = Some(ExpressionType::CompileError);
               }
            }
            None => {
               validation_context.error_count += 1;
               eprintln!("Encountered call to undefined procedure/function `{}`", name);
               expr_node.exp_type = Some(ExpressionType::CompileError);
            }
         }

         for arg in args {
            do_type(arg, validation_context);
         }
      }
   }
}
