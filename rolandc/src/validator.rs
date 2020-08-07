use super::type_data::{ExpressionType, ValueType};
use crate::parse::{BinOp, BlockNode, Expression, ExpressionNode, Program, Statement, UnOp};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
enum TypeValidator {
   Bool,
   AnyInt,
   AnyPointer,
   Any,
}

fn matches(type_validation: &TypeValidator, et: &ExpressionType) -> bool {
   match (type_validation, et) {
      (TypeValidator::Any, _) => true,
      (TypeValidator::AnyPointer, ExpressionType::Pointer(_, _)) => true,
      (TypeValidator::Bool, ExpressionType::Value(ValueType::Bool)) => true,
      (TypeValidator::AnyInt, ExpressionType::Value(ValueType::Int(_))) => true,
      (TypeValidator::AnyInt, ExpressionType::Value(ValueType::UnknownInt)) => true,
      _ => false,
   }
}

fn any_match(type_validations: &[TypeValidator], et: &ExpressionType) -> bool {
   let mut any_match = false;
   for type_validation in type_validations.iter() {
      any_match |= matches(type_validation, et);
   }
   any_match
}

struct ProcedureInfo {
   pure: bool,
   parameters: Vec<ExpressionType>,
   ret_type: ExpressionType,
}

struct ValidationContext<'a> {
   procedure_info: &'a HashMap<String, ProcedureInfo>,
   cur_procedure_info: Option<&'a ProcedureInfo>,
   string_literals: HashSet<String>,
   variable_types: HashMap<String, (ExpressionType, u64)>,
   error_count: u64,
   block_depth: u64,
   unknown_ints: u64,
}

pub fn type_and_check_validity(program: &mut Program) -> u64 {
   let mut procedure_info = HashMap::new();
   let mut error_count = 0;
   // Built-In functions
   let standard_lib_procs = [(
      "print",
      false,
      &[ExpressionType::Value(ValueType::String)],
      ExpressionType::Value(ValueType::Unit),
   )];
   for p in standard_lib_procs.iter() {
      procedure_info.insert(
         p.0.to_string(),
         ProcedureInfo {
            pure: p.1,
            parameters: p.2.to_vec(),
            ret_type: p.3.clone(),
         },
      );
   }

   for procedure in program.procedures.iter() {
      match procedure_info.insert(
         procedure.name.clone(),
         ProcedureInfo {
            pure: procedure.pure,
            parameters: procedure.parameters.iter().map(|x| x.1.clone()).collect(),
            ret_type: procedure.ret_type.clone(),
         },
      ) {
         Some(_) => {
            error_count += 1;
            eprintln!(
               "Encountered duplicate procedures/functions with the same name `{}`",
               procedure.name
            );
         }
         None => (),
      }
   }

   let mut validation_context = ValidationContext {
      string_literals: HashSet::new(),
      variable_types: HashMap::new(),
      error_count,
      procedure_info: &procedure_info,
      cur_procedure_info: None,
      block_depth: 0,
      unknown_ints: 0,
   };

   if !validation_context.procedure_info.contains_key("main") {
      validation_context.error_count += 1;
      eprintln!("A procedure with the name `main` must be present");
   } else if validation_context.procedure_info.get("main").unwrap().ret_type != ExpressionType::Value(ValueType::Unit) {
      validation_context.error_count += 1;
      eprintln!("`main` is a special procedure and is not allowed to return a value");
   }

   // We won't proceed with type checking because there could be false positives due to
   // procedure definition errors.
   if validation_context.error_count > 0 {
      return validation_context.error_count;
   }

   for procedure in program.procedures.iter_mut() {
      validation_context.variable_types.clear();
      validation_context.cur_procedure_info = procedure_info.get(procedure.name.as_str());

      for parameter in procedure.parameters.iter() {
         // TODO, again, interning
         validation_context
            .variable_types
            .insert(parameter.0.clone(), (parameter.1.clone(), 0));
         procedure.locals.insert(parameter.0.clone(), parameter.1.clone());
      }

      type_block(&mut procedure.block, &mut validation_context, &mut procedure.locals);

      // Ensure that the last statement is a return statement
      // (it has already been type checked, so we don't have to check that)
      match (&procedure.ret_type, procedure.block.statements.last()) {
         (ExpressionType::Value(ValueType::Unit), _) => (),
         (_, Some(Statement::ReturnStatement(_))) => (),
         (x, _) => {
            validation_context.error_count += 1;
            eprintln!(
               "Procedure/function `{}` is declared to return type {} but is missing a final return statement",
               procedure.name,
               x.as_roland_type_info()
            );
         }
      }
   }

   if validation_context.unknown_ints > 0 {
      validation_context.error_count += 1;
      eprintln!(
         "We weren't able to determine the types of {} int literals",
         validation_context.unknown_ints
      );
   }

   program.literals = validation_context.string_literals;

   validation_context.error_count
}

fn type_statement(
   statement: &mut Statement,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut HashMap<String, ExpressionType>,
) {
   match statement {
      Statement::AssignmentStatement(len, en) => {
         do_type(len, validation_context);
         do_type(en, validation_context);

         // Type inference
         if len.exp_type.as_ref().unwrap().is_any_known_int()
            && en.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::UnknownInt)
         {
            set_inferred_type(len.exp_type.clone().unwrap(), en, validation_context);
         }

         let lhs_type = len.exp_type.as_ref().unwrap();
         let rhs_type = en.exp_type.as_ref().unwrap();

         if lhs_type != rhs_type {
            validation_context.error_count += 1;
            eprintln!(
               "Left hand side of assignment has type {} which does not match the type of the right hand side {}",
               lhs_type.as_roland_type_info(),
               rhs_type.as_roland_type_info(),
            );
         } else if !len.expression.is_lvalue() {
            validation_context.error_count += 1;
            eprintln!(
               "Left hand side of assignment is not a valid memory location; i.e. a variable or parameter",
            );
         }
      }
      Statement::BlockStatement(bn) => {
         type_block(bn, validation_context, cur_procedure_locals);
      }
      Statement::ExpressionStatement(en) => {
         do_type(en, validation_context);
      }
      Statement::IfElseStatement(en, block_1, block_2) => {
         type_block(block_1, validation_context, cur_procedure_locals);
         type_statement(block_2, validation_context, cur_procedure_locals);
         do_type(en, validation_context);
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if if_exp_type != &ExpressionType::Value(ValueType::Bool)
            && if_exp_type != &ExpressionType::Value(ValueType::CompileError)
         {
            validation_context.error_count += 1;
            eprintln!(
               "Value of if expression must be a bool; instead got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info()
            );
         }
      }
      Statement::ReturnStatement(en) => {
         do_type(en, validation_context);
         let cur_procedure_info = validation_context.cur_procedure_info.unwrap();

         // Type Inference
         if *en.exp_type.as_ref().unwrap() == ExpressionType::Value(ValueType::UnknownInt)
            && cur_procedure_info.ret_type.is_any_known_int()
         {
            set_inferred_type(cur_procedure_info.ret_type.clone(), en, validation_context);
         }

         if en.exp_type.as_ref().unwrap().is_concrete_type()
            && en.exp_type.as_ref().unwrap() != &cur_procedure_info.ret_type
         {
            validation_context.error_count += 1;
            eprintln!(
               "Value of return statement must match declared return type {}; got {}",
               cur_procedure_info.ret_type.as_roland_type_info(),
               en.exp_type.as_ref().unwrap().as_roland_type_info()
            );
         }
      }
      Statement::VariableDeclaration(id, en, dt) => {
         let declared_type_is_known_int = dt.as_ref().map(|x| x.is_any_known_int()).unwrap_or(false);

         do_type(en, validation_context);

         let result_type = if en.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::UnknownInt)
            && declared_type_is_known_int
         {
            set_inferred_type(dt.clone().unwrap(), en, validation_context);
            dt.clone().unwrap()
         } else if dt.is_some() && *dt != en.exp_type {
            validation_context.error_count += 1;
            eprintln!(
               "Declared type {} does not match actual expression type {}",
               dt.as_ref().unwrap().as_roland_type_info(),
               en.exp_type.as_ref().unwrap().as_roland_type_info()
            );
            ExpressionType::Value(ValueType::CompileError)
         } else {
            en.exp_type.clone().unwrap()
         };

         if validation_context.variable_types.contains_key(id) {
            validation_context.error_count += 1;
            eprintln!("Variable shadowing is not supported at this time (`{}`)", id);
         } else {
            validation_context.variable_types.insert(
               id.clone(),
               (en.exp_type.clone().unwrap(), validation_context.block_depth),
            );
            // TODO, again, interning
            cur_procedure_locals.insert(id.clone(), result_type);
         }
      }
   }
}

fn type_block(
   bn: &mut BlockNode,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut HashMap<String, ExpressionType>,
) {
   validation_context.block_depth += 1;

   for statement in bn.statements.iter_mut() {
      type_statement(statement, validation_context, cur_procedure_locals);
   }

   validation_context.block_depth -= 1;
   let cur_block_depth = validation_context.block_depth;
   validation_context.variable_types.retain(|_, v| v.1 <= cur_block_depth);
}

fn do_type(expr_node: &mut ExpressionNode, validation_context: &mut ValidationContext) {
   match &mut expr_node.expression {
      Expression::BoolLiteral(_) => {
         expr_node.exp_type = Some(ExpressionType::Value(ValueType::Bool));
      }
      Expression::IntLiteral(_) => {
         validation_context.unknown_ints += 1;
         expr_node.exp_type = Some(ExpressionType::Value(ValueType::UnknownInt));
      }
      Expression::StringLiteral(lit) => {
         // This clone will become cheap when we intern everywhere
         validation_context.string_literals.insert(lit.clone());
         expr_node.exp_type = Some(ExpressionType::Value(ValueType::String));
      }
      Expression::BinaryOperator(bin_op, e) => {
         do_type(&mut e.0, validation_context);
         do_type(&mut e.1, validation_context);

         let correct_arg_types: &[TypeValidator] = match bin_op {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::GreaterThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThan
            | BinOp::LessThanOrEqualTo => &[TypeValidator::AnyInt],
            BinOp::Equality | BinOp::NotEquality | BinOp::BitwiseAnd | BinOp::BitwiseOr => &[TypeValidator::AnyInt, TypeValidator::Bool],
         };

         // Type inference
         if e.0.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::UnknownInt)
            && e.1.exp_type.as_ref().unwrap().is_any_known_int()
         {
            set_inferred_type(e.1.exp_type.clone().unwrap(), &mut e.0, validation_context);
         } else if e.0.exp_type.as_ref().unwrap().is_any_known_int()
            && e.1.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::UnknownInt)
         {
            set_inferred_type(e.0.exp_type.clone().unwrap(), &mut e.1, validation_context);
         }

         let lhs_type = e.0.exp_type.as_ref().unwrap();
         let rhs_type = e.1.exp_type.as_ref().unwrap();

         let result_type = if lhs_type == &ExpressionType::Value(ValueType::CompileError)
            || rhs_type == &ExpressionType::Value(ValueType::CompileError)
         {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_arg_types, lhs_type) {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {}",
               bin_op,
               correct_arg_types,
               lhs_type.as_roland_type_info()
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_arg_types, rhs_type) {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires RHS to have type matching {:?}; instead got {}",
               bin_op,
               correct_arg_types,
               rhs_type.as_roland_type_info()
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if lhs_type != rhs_type {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS and RHS to have identical type; instead got {} and {}",
               bin_op,
               lhs_type.as_roland_type_info(),
               rhs_type.as_roland_type_info()
            );
            ExpressionType::Value(ValueType::CompileError)
         } else {
            match bin_op {
               BinOp::Add | BinOp::Subtract | BinOp::Multiply | BinOp::Divide | BinOp::BitwiseAnd | BinOp::BitwiseOr => lhs_type.clone(),
               BinOp::Equality
               | BinOp::NotEquality
               | BinOp::GreaterThan
               | BinOp::GreaterThanOrEqualTo
               | BinOp::LessThan
               | BinOp::LessThanOrEqualTo => ExpressionType::Value(ValueType::Bool),
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::UnaryOperator(un_op, e) => {
         do_type(e, validation_context);

         let (correct_type, node_type) = match un_op {
            UnOp::Dereference => {
               let mut new_type = e.exp_type.clone().unwrap();
               // If this fails, it will be caught by the type matcher
               let _ = new_type.decrement_indirection_count();
               (TypeValidator::AnyPointer, new_type)
            },
            UnOp::Negate => (TypeValidator::AnyInt, e.exp_type.clone().unwrap()),
            UnOp::LogicalNegate => (TypeValidator::Bool, e.exp_type.clone().unwrap()),
            UnOp::AddressOf => {
               let mut new_type = e.exp_type.clone().unwrap();
               new_type.increment_indirection_count();
               (TypeValidator::Any, new_type)
            }
         };

         let result_type = if e.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::CompileError) {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else if !matches(&correct_type, e.exp_type.as_ref().unwrap()) {
            validation_context.error_count += 1;
            eprintln!(
               "Expected type {:?} for expression {:?}; instead got {}",
               correct_type,
               un_op,
               e.exp_type.as_ref().unwrap().as_roland_type_info()
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::AddressOf && !e.expression.is_lvalue() {
            validation_context.error_count += 1;
            eprintln!("A pointer can only be taken to a value that resides in memory; i.e. a variable or parameter");
            ExpressionType::Value(ValueType::CompileError)
         } else {
            node_type
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::Variable(id) => {
         let defined_type = validation_context.variable_types.get(id);

         let result_type = match defined_type {
            Some(t) => t.0.clone(),
            None => {
               validation_context.error_count += 1;
               eprintln!("Encountered undefined variable `{}`", id);
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::ProcedureCall(name, args) => {
         for arg in args.iter_mut() {
            do_type(arg, validation_context);
         }

         if name == "main" {
            validation_context.error_count += 1;
            eprintln!("`main` is a special procedure and is not allowed to be called");
         }

         match validation_context.procedure_info.get(name) {
            Some(procedure_info) => {
               expr_node.exp_type = Some(procedure_info.ret_type.clone());

               if validation_context.cur_procedure_info.unwrap().pure && !procedure_info.pure {
                  validation_context.error_count += 1;
                  eprintln!("Encountered call to procedure `{}` (impure) in func (pure)", name);
               }

               if procedure_info.parameters.len() != args.len() {
                  validation_context.error_count += 1;
                  eprintln!(
                     "In call to `{}`, mismatched arity. Expected {} arguments but got {}",
                     name,
                     procedure_info.parameters.len(),
                     args.len()
                  );
               // We shortcircuit here, because there will likely be lots of mistmatched types if an arg was forgotten
               } else {
                  let actual_types = args.iter_mut();
                  let expected_types = procedure_info.parameters.iter();
                  for (actual, expected) in actual_types.zip(expected_types) {
                     // Type Inference
                     if *actual.exp_type.as_ref().unwrap() == ExpressionType::Value(ValueType::UnknownInt)
                        && expected.is_any_known_int()
                     {
                        set_inferred_type(expected.clone(), actual, validation_context);
                     }

                     let actual_type = actual.exp_type.as_ref().unwrap();
                     if actual_type != expected && *actual_type != ExpressionType::Value(ValueType::CompileError) {
                        validation_context.error_count += 1;
                        eprintln!(
                           "In call to `{}`, encountered argument of type {} when we expected {}",
                           name,
                           actual_type.as_roland_type_info(),
                           expected.as_roland_type_info()
                        );
                     }
                  }
               }
            }
            None => {
               validation_context.error_count += 1;
               eprintln!("Encountered call to undefined procedure/function `{}`", name);
               expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
            }
         }
      }
   }
}

fn set_inferred_type(
   e_type: ExpressionType,
   expr_node: &mut ExpressionNode,
   validation_context: &mut ValidationContext,
) {
   if expr_node.exp_type.as_ref().unwrap() != &ExpressionType::Value(ValueType::UnknownInt) {
      return;
   }
   match &mut expr_node.expression {
      Expression::BoolLiteral(_) => unreachable!(),
      Expression::IntLiteral(_) => {
         validation_context.unknown_ints -= 1;
         expr_node.exp_type = Some(e_type);
      }
      Expression::StringLiteral(_) => unreachable!(),
      Expression::BinaryOperator(_, e) => {
         set_inferred_type(e_type.clone(), &mut e.0, validation_context);
         set_inferred_type(e_type.clone(), &mut e.1, validation_context);
         expr_node.exp_type = Some(e_type);
      }
      Expression::UnaryOperator(_, e) => {
         set_inferred_type(e_type.clone(), e, validation_context);
         expr_node.exp_type = Some(e_type);
      }
      Expression::Variable(_) => unreachable!(),
      Expression::ProcedureCall(_, _) => unreachable!(),
   }
}
