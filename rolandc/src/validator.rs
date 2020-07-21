use crate::parse::{
   BinOp, BlockNode, Expression, ExpressionNode, ExpressionType, Program, Statement, UnOp,
};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
enum TypeValidator {
   Bool,
   AnyInt,
}

fn matches(type_validation: &TypeValidator, et: &ExpressionType) -> bool {
   match (type_validation, et) {
      (TypeValidator::Bool, ExpressionType::Bool) => true,
      (TypeValidator::AnyInt, ExpressionType::Int(_)) => true,
      (TypeValidator::AnyInt, ExpressionType::UnknownInt) => true,
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
}

struct ValidationContext {
   string_literals: HashSet<String>,
   procedure_info: HashMap<String, ProcedureInfo>,
   variable_types: HashMap<String, (ExpressionType, u64)>,
   error_count: u64,
   in_pure_func: bool,
   block_depth: u64,
   unknown_ints: u64,
}

pub fn type_and_check_validity(program: &mut Program) -> u64 {
   let mut validation_context = ValidationContext {
      string_literals: HashSet::new(),
      variable_types: HashMap::new(),
      error_count: 0,
      procedure_info: HashMap::new(),
      in_pure_func: false,
      block_depth: 0,
      unknown_ints: 0,
   };

   // Built-In functions
   let standard_lib_procs = [("print", false, &[ExpressionType::String])];
   for p in standard_lib_procs.iter() {
      validation_context.procedure_info.insert(
         p.0.to_string(),
         ProcedureInfo {
            pure: p.1,
            parameters: p.2.to_vec(),
         },
      );
   }

   for procedure in program.procedures.iter() {
      match validation_context.procedure_info.insert(
         procedure.name.clone(),
         ProcedureInfo {
            pure: procedure.pure,
            parameters: procedure.parameters.iter().map(|x| x.1.clone()).collect(),
         },
      ) {
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

   if !validation_context.procedure_info.contains_key("main") {
      validation_context.error_count += 1;
      eprintln!("A procedure with the name `main` must be present");
   }

   // We won't proceed with type checking because there could be false positives due to
   // procedure definition errors.
   if validation_context.error_count > 0 {
      return validation_context.error_count;
   }

   for procedure in program.procedures.iter_mut() {
      validation_context.variable_types.clear();
      validation_context.in_pure_func = procedure.pure;

      for parameter in procedure.parameters.iter() {
         validation_context
            .variable_types
            .insert(parameter.0.clone(), (parameter.1.clone(), 0));
      }

      type_block(&mut procedure.block, &mut validation_context, &mut procedure.locals)
   }

   if validation_context.unknown_ints > 0 {
      validation_context.error_count += 1;
      eprintln!("We weren't able to determine the types of {} int literals", validation_context.unknown_ints);
   }

   program.literals = validation_context.string_literals;

   validation_context.error_count
}

fn type_block(
   bn: &mut BlockNode,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut Vec<(String, ExpressionType)>,
) {
   validation_context.block_depth += 1;

   for statement in bn.statements.iter_mut() {
      match statement {
         Statement::BlockStatement(bn) => {
            type_block(bn, validation_context, cur_procedure_locals);
         }
         Statement::VariableDeclaration(id, en, dt) => {
            let declared_type_is_known_int = dt.as_ref().map(|x| x.is_any_known_int()).unwrap_or(false);

            do_type(en, validation_context);

            let result_type = if en.exp_type.as_ref().unwrap() == &ExpressionType::UnknownInt && declared_type_is_known_int {
               set_inferred_type(dt.as_ref().unwrap(), en, validation_context);
               dt.clone().unwrap()
            } else if dt.is_some() && *dt != en.exp_type {
               validation_context.error_count += 1;
               eprintln!("Declared type {} does not match actual expression type {}", dt.as_ref().unwrap().as_roland_type(), en.exp_type.as_ref().unwrap().as_roland_type());
               ExpressionType::CompileError
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
               cur_procedure_locals.push((id.clone(), result_type));
            }
         }
         Statement::ExpressionStatement(en) => {
            do_type(en, validation_context);
         }
         Statement::IfElseStatement(en, block_1, block_2) => {
            type_block(block_1, validation_context, cur_procedure_locals);
            type_block(block_2, validation_context, cur_procedure_locals);
            do_type(en, validation_context);
            let if_exp_type = en.exp_type.as_ref().unwrap();
            if if_exp_type != &ExpressionType::Bool && if_exp_type != &ExpressionType::CompileError {
               validation_context.error_count += 1;
               eprintln!(
                  "Value of if expression must be a bool; instead got {}",
                  en.exp_type.as_ref().unwrap().as_roland_type()
               );
            }
         }
      }
   }

   validation_context.block_depth -= 1;
   let cur_block_depth = validation_context.block_depth;
   validation_context.variable_types.retain(|_, v| v.1 <= cur_block_depth);
}

fn do_type(expr_node: &mut ExpressionNode, validation_context: &mut ValidationContext) {
   match &mut expr_node.expression {
      Expression::BoolLiteral(_) => {
         expr_node.exp_type = Some(ExpressionType::Bool);
      }
      Expression::IntLiteral(_) => {
         validation_context.unknown_ints += 1;
         expr_node.exp_type = Some(ExpressionType::UnknownInt);
      }
      Expression::StringLiteral(lit) => {
         // This clone will become cheap when we intern everywhere
         validation_context.string_literals.insert(lit.clone());
         expr_node.exp_type = Some(ExpressionType::String);
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
            BinOp::Equality | BinOp::NotEquality => &[TypeValidator::AnyInt, TypeValidator::Bool],
         };

         let lhs_type = e.0.exp_type.as_ref().unwrap();
         let rhs_type = e.1.exp_type.as_ref().unwrap();

         let result_type = if lhs_type == &ExpressionType::CompileError || rhs_type == &ExpressionType::CompileError {
            // Avoid cascading errors
            ExpressionType::CompileError
         } else if lhs_type == &ExpressionType::UnknownInt && rhs_type.is_any_known_int() {
            // todo - do we want to keep this? currently never hit, would require special syntax such as 1234i64
            set_inferred_type(rhs_type, &mut e.0, validation_context);
            rhs_type.clone()
         } else if lhs_type.is_any_known_int() && rhs_type == &ExpressionType::UnknownInt {
            // todo - do we want to keep this? currently never hit, would require special syntax such as 1234i64
            set_inferred_type(lhs_type, &mut e.1, validation_context);
            lhs_type.clone()
         } else if !any_match(correct_arg_types, lhs_type) {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {}",
               bin_op,
               correct_arg_types,
               e.0.exp_type.as_ref().unwrap().as_roland_type()
            );
            ExpressionType::CompileError
         } else if !any_match(correct_arg_types, rhs_type) {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {}",
               bin_op,
               correct_arg_types,
               e.1.exp_type.as_ref().unwrap().as_roland_type()
            );
            ExpressionType::CompileError
         } else if lhs_type != rhs_type {
            validation_context.error_count += 1;
            eprintln!(
               "Binary operator {:?} requires LHS and RHS to have identical type; instead got {} and {}",
               bin_op,
               e.0.exp_type.as_ref().unwrap().as_roland_type(),
               e.1.exp_type.as_ref().unwrap().as_roland_type()
            );
            ExpressionType::CompileError
         } else {
            match bin_op {
               BinOp::Add | BinOp::Subtract | BinOp::Multiply | BinOp::Divide => lhs_type.clone(),
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
            UnOp::Negate => TypeValidator::AnyInt,
            UnOp::LogicalNegate => TypeValidator::Bool,
         };

         let result_type = if e.exp_type.as_ref().unwrap() == &ExpressionType::CompileError {
            // Avoid cascading errors
            ExpressionType::CompileError
         } else if !matches(&correct_type, e.exp_type.as_ref().unwrap()) {
            validation_context.error_count += 1;
            eprintln!(
               "Expected type {:?} for expression {:?}; instead got {}",
               correct_type,
               un_op,
               e.exp_type.as_ref().unwrap().as_roland_type()
            );
            ExpressionType::CompileError
         } else {
            e.exp_type.clone().unwrap()
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::Variable(id) => {
         let defined_type = validation_context.variable_types.get(id);

         let result_type = match defined_type {
            Some(t) => t.0.clone(),
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

         for arg in args.iter_mut() {
            do_type(arg, validation_context);
         }

         match validation_context.procedure_info.get(name) {
            Some(procedure_info) => {
               if validation_context.in_pure_func && !procedure_info.pure {
                  validation_context.error_count += 1;
                  eprintln!("Encountered call to procedure `{}` (impure) in func (pure)", name);
                  expr_node.exp_type = Some(ExpressionType::CompileError);
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
                  let actual_types = args.iter().map(|x| x.exp_type.as_ref().unwrap());
                  let expected_types = procedure_info.parameters.iter();
                  for (actual, expected) in actual_types.zip(expected_types) {
                     if actual != expected && *actual != ExpressionType::CompileError {
                        validation_context.error_count += 1;
                        eprintln!(
                           "In call to `{}`, encountered argument of type {} when we expected {}",
                           name,
                           actual.as_roland_type(),
                           expected.as_roland_type()
                        );
                     }
                  }
               }
            }
            None => {
               validation_context.error_count += 1;
               eprintln!("Encountered call to undefined procedure/function `{}`", name);
               expr_node.exp_type = Some(ExpressionType::CompileError);
            }
         }
      }
   }
}

fn set_inferred_type(e_type: &ExpressionType, expr_node: &mut ExpressionNode, validation_context: &mut ValidationContext) {
   if expr_node.exp_type.as_ref().unwrap() != &ExpressionType::UnknownInt {
      return;
   }
   match &mut expr_node.expression {
      Expression::BoolLiteral(_) => unreachable!(),
      Expression::IntLiteral(_) => {
         validation_context.unknown_ints -= 1;
         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::StringLiteral(_) => unreachable!(),
      Expression::BinaryOperator(_, e) => {
         set_inferred_type(e_type, &mut e.0, validation_context);
         set_inferred_type(e_type, &mut e.1, validation_context);
         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::UnaryOperator(_, e) => {
         set_inferred_type(e_type, e, validation_context);
         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::Variable(_) => unreachable!(),
      Expression::ProcedureCall(_, _) => unreachable!(),
   }
}
