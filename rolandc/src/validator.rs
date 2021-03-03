use super::type_data::{ExpressionType, ValueType};
use crate::lex::SourceInfo;
use crate::parse::{BinOp, BlockNode, Expression, ExpressionNode, Program, Statement, UnOp};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};
use std::io::Write;

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
   procedure_begin_location: SourceInfo,
}

pub struct StructInfo {
   pub field_types: HashMap<String, ExpressionType>,
   pub struct_begin_location: SourceInfo,
}

struct ValidationContext<'a> {
   // todo: for reliable output, this probably also needs to become and index map
   procedure_info: &'a IndexMap<String, ProcedureInfo>,
   struct_info: &'a IndexMap<String, StructInfo>,
   cur_procedure_info: Option<&'a ProcedureInfo>,
   string_literals: HashSet<String>,
   variable_types: HashMap<String, (ExpressionType, u64)>,
   error_count: u64,
   block_depth: u64,
   loop_depth: u64,
   unknown_ints: u64,
}

fn recursive_struct_check(
   base_name: &str,
   struct_fields: &HashMap<String, ExpressionType>,
   struct_info: &IndexMap<String, StructInfo>,
) -> bool {
   let mut is_recursive = false;

   for struct_field in struct_fields.iter().flat_map(|x| match &x.1 {
      ExpressionType::Value(ValueType::Struct(x)) => Some(x.as_str()),
      _ => None,
   }) {
      if struct_field == base_name {
         is_recursive = true;
         break;
      }

      is_recursive |= struct_info
         .get(struct_field)
         .map(|si| recursive_struct_check(base_name, &si.field_types, struct_info))
         .unwrap_or(false);
   }

   is_recursive
}

pub fn type_and_check_validity<W: Write>(program: &mut Program, err_stream: &mut W) -> u64 {
   let mut procedure_info: IndexMap<String, ProcedureInfo> = IndexMap::new();
   let mut struct_info: IndexMap<String, StructInfo> = IndexMap::new();
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
            procedure_begin_location: SourceInfo {
               line: 0,
               col: 0,
            },
         },
      );
   }

   let mut parameter_dupe_check = HashSet::new();
   for procedure in program.procedures.iter() {
      parameter_dupe_check.clear();
      parameter_dupe_check.reserve(procedure.parameters.len());
      for param in procedure.parameters.iter() {
         if !parameter_dupe_check.insert(param.0.as_str()) {
            error_count += 1;
            writeln!(
               err_stream,
               "Procedure/function `{}` has a duplicate parameter `{}`",
               procedure.name, param.0,
            )
            .unwrap();
            writeln!(err_stream, "↳ procedure/function defined @ line {}, column {}", procedure.procedure_begin_location.line, procedure.procedure_begin_location.col).unwrap();
         } 
      }

      match procedure_info.insert(
         procedure.name.clone(),
         ProcedureInfo {
            pure: procedure.pure,
            parameters: procedure.parameters.iter().map(|x| x.1.clone()).collect(),
            ret_type: procedure.ret_type.clone(),
            procedure_begin_location: procedure.procedure_begin_location,
         },
      ) {
         Some(old_procedure) => {
            error_count += 1;
            writeln!(
               err_stream,
               "Encountered duplicate procedures/functions with the same name `{}`",
               procedure.name
            )
            .unwrap();
            writeln!(err_stream, "↳ first procedure/function defined @ line {}, column {}", old_procedure.procedure_begin_location.line, old_procedure.procedure_begin_location.col).unwrap();
            writeln!(err_stream, "↳ second procedure/function defined @ line {}, column {}", procedure.procedure_begin_location.line, procedure.procedure_begin_location.col).unwrap();
         }
         None => (),
      }
   }

   for a_struct in program.structs.iter() {
      let mut field_map = HashMap::with_capacity(a_struct.fields.len());
      for field in a_struct.fields.iter() {
         match field_map.insert(field.0.clone(), field.1.clone()) {
            Some(__) => {
               error_count += 1;
               writeln!(
                  err_stream,
                  "Struct `{}` has a duplicate field `{}`",
                  a_struct.name, field.0,
               )
               .unwrap();
               writeln!(err_stream, "↳ struct defined @ line {}, column {}", a_struct.struct_begin_location.line, a_struct.struct_begin_location.col).unwrap();
            }
            None => (),
         }
      }

      match struct_info.insert(a_struct.name.clone(), StructInfo {
         field_types: field_map,
         struct_begin_location: a_struct.struct_begin_location,
      }) {
         Some(old_struct) => {
            error_count += 1;
            writeln!(
               err_stream,
               "Encountered duplicate structs with the same name `{}`",
               a_struct.name
            )
            .unwrap();
            writeln!(err_stream, "↳ first struct defined @ line {}, column {}", old_struct.struct_begin_location.line, old_struct.struct_begin_location.col).unwrap();
            writeln!(err_stream, "↳ second struct defined @ line {}, column {}", a_struct.struct_begin_location.line, a_struct.struct_begin_location.col).unwrap();
         }
         None => (),
      }
   }

   for struct_i in struct_info.iter() {
      for (field, e_type) in struct_i.1.field_types.iter().filter(|(_, e_type)| match e_type {
         ExpressionType::Value(ValueType::Struct(s)) => struct_info.get(s).is_none(),
         _ => false,
      }) {
         error_count += 1;
         writeln!(
            err_stream,
            "Field `{}` of struct `{}` is of undeclared type `{}`",
            field,
            struct_i.0,
            e_type.as_roland_type_info(),
         )
         .unwrap();
      }

      if recursive_struct_check(struct_i.0.as_str(), &struct_i.1.field_types, &struct_info) {
         error_count += 1;
         writeln!(
            err_stream,
            "Struct `{}` contains itself, which isn't allowed as it would result in an infinitely large struct",
            struct_i.0.as_str(),
         )
         .unwrap();
      }
   }

   let mut validation_context = ValidationContext {
      string_literals: HashSet::new(),
      variable_types: HashMap::new(),
      error_count,
      procedure_info: &procedure_info,
      struct_info: &struct_info,
      cur_procedure_info: None,
      block_depth: 0,
      loop_depth: 0,
      unknown_ints: 0,
   };

   if !validation_context.procedure_info.contains_key("main") {
      validation_context.error_count += 1;
      writeln!(err_stream, "A procedure with the name `main` must be present").unwrap();
   } else if validation_context.procedure_info.get("main").unwrap().ret_type != ExpressionType::Value(ValueType::Unit) {
      validation_context.error_count += 1;
      writeln!(
         err_stream,
         "`main` is a special procedure and is not allowed to return a value"
      )
      .unwrap();
      let si = validation_context.procedure_info.get("main").unwrap().procedure_begin_location;
      writeln!(err_stream, "↳ main defined @ line {}, column {}", si.line, si.col).unwrap();
   }

   // We won't proceed with type checking because there could be false positives due to
   // procedure/struct definition errors.
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

      type_block(
         err_stream,
         &mut procedure.block,
         &mut validation_context,
         &mut procedure.locals,
      );

      // Ensure that the last statement is a return statement
      // (it has already been type checked, so we don't have to check that)
      match (&procedure.ret_type, procedure.block.statements.last()) {
         (ExpressionType::Value(ValueType::Unit), _) => (),
         (_, Some(Statement::ReturnStatement(_))) => (),
         (x, _) => {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Procedure/function `{}` is declared to return type {} but is missing a final return statement",
               procedure.name,
               x.as_roland_type_info()
            )
            .unwrap();
            writeln!(err_stream, "↳ procedure/function defined @ line {}, column {}", procedure.procedure_begin_location.line, procedure.procedure_begin_location.col).unwrap();
         }
      }
   }

   if validation_context.unknown_ints > 0 {
      validation_context.error_count += 1;
      writeln!(
         err_stream,
         "We weren't able to determine the types of {} int literals",
         validation_context.unknown_ints
      )
      .unwrap();
   }

   let err_count = validation_context.error_count;
   program.literals = validation_context.string_literals;
   program.struct_info = struct_info;

   err_count
}

fn type_statement<W: Write>(
   err_stream: &mut W,
   statement: &mut Statement,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut IndexMap<String, ExpressionType>,
) {
   match statement {
      Statement::AssignmentStatement(len, en) => {
         do_type(err_stream, len, validation_context);
         do_type(err_stream, en, validation_context);

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
            writeln!(
               err_stream,
               "Left hand side of assignment has type {} which does not match the type of the right hand side {}",
               lhs_type.as_roland_type_info(),
               rhs_type.as_roland_type_info(),
            )
            .unwrap();
         } else if !len.expression.is_lvalue() {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Left hand side of assignment is not a valid memory location; i.e. a variable, field, or parameter"
            )
            .unwrap();
         }
      }
      Statement::BlockStatement(bn) => {
         type_block(err_stream, bn, validation_context, cur_procedure_locals);
      }
      Statement::ContinueStatement => {
         if validation_context.loop_depth == 0 {
            validation_context.error_count += 1;
            writeln!(err_stream, "Continue statement can only be used in a loop").unwrap();
         }
      }
      Statement::BreakStatement => {
         if validation_context.loop_depth == 0 {
            validation_context.error_count += 1;
            writeln!(err_stream, "Break statement can only be used in a loop").unwrap();
         }
      }
      Statement::LoopStatement(bn) => {
         validation_context.loop_depth += 1;
         type_block(err_stream, bn, validation_context, cur_procedure_locals);
         validation_context.loop_depth -= 1;
      }
      Statement::ExpressionStatement(en) => {
         do_type(err_stream, en, validation_context);
      }
      Statement::IfElseStatement(en, block_1, block_2) => {
         type_block(err_stream, block_1, validation_context, cur_procedure_locals);
         type_statement(err_stream, block_2, validation_context, cur_procedure_locals);
         do_type(err_stream, en, validation_context);
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if if_exp_type != &ExpressionType::Value(ValueType::Bool)
            && if_exp_type != &ExpressionType::Value(ValueType::CompileError)
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Value of if expression must be a bool; instead got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info()
            )
            .unwrap();
         }
      }
      Statement::ReturnStatement(en) => {
         do_type(err_stream, en, validation_context);
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
            writeln!(
               err_stream,
               "Value of return statement must match declared return type {}; got {}",
               cur_procedure_info.ret_type.as_roland_type_info(),
               en.exp_type.as_ref().unwrap().as_roland_type_info()
            )
            .unwrap();
         }
      }
      Statement::VariableDeclaration(id, en, dt) => {
         let declared_type_is_known_int = dt.as_ref().map(|x| x.is_any_known_int()).unwrap_or(false);

         do_type(err_stream, en, validation_context);

         let result_type = if en.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::UnknownInt)
            && declared_type_is_known_int
         {
            set_inferred_type(dt.clone().unwrap(), en, validation_context);
            dt.clone().unwrap()
         } else if dt.is_some()
            && *dt != en.exp_type
            && en.exp_type != Some(ExpressionType::Value(ValueType::CompileError))
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Declared type {} does not match actual expression type {}",
               dt.as_ref().unwrap().as_roland_type_info(),
               en.exp_type.as_ref().unwrap().as_roland_type_info()
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else if dt
            .as_ref()
            .and_then(|x| match x {
               ExpressionType::Value(ValueType::Struct(s)) => Some(s),
               _ => None,
            })
            .map(|x| validation_context.struct_info.get(x).is_none())
            .unwrap_or(false)
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Variable `{}` is declared with undeclared type `{}`",
               id,
               dt.as_ref().unwrap().as_roland_type_info()
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else {
            en.exp_type.clone().unwrap()
         };

         if validation_context.variable_types.contains_key(id) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Variable shadowing is not supported at this time (`{}`)",
               id
            )
            .unwrap();
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

fn type_block<W: Write>(
   err_stream: &mut W,
   bn: &mut BlockNode,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut IndexMap<String, ExpressionType>,
) {
   validation_context.block_depth += 1;

   for statement in bn.statements.iter_mut() {
      type_statement(err_stream, statement, validation_context, cur_procedure_locals);
   }

   validation_context.block_depth -= 1;
   let cur_block_depth = validation_context.block_depth;
   validation_context.variable_types.retain(|_, v| v.1 <= cur_block_depth);
}

fn do_type<W: Write>(err_stream: &mut W, expr_node: &mut ExpressionNode, validation_context: &mut ValidationContext) {
   match &mut expr_node.expression {
      Expression::UnitLiteral => {
         expr_node.exp_type = Some(ExpressionType::Value(ValueType::Unit));
      }
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
         do_type(err_stream, &mut e.0, validation_context);
         do_type(err_stream, &mut e.1, validation_context);

         let correct_arg_types: &[TypeValidator] = match bin_op {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::GreaterThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThan
            | BinOp::LessThanOrEqualTo => &[TypeValidator::AnyInt],
            BinOp::Equality | BinOp::NotEquality | BinOp::BitwiseAnd | BinOp::BitwiseOr | BinOp::BitwiseXor => {
               &[TypeValidator::AnyInt, TypeValidator::Bool]
            }
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
            writeln!(
               err_stream,
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {}",
               bin_op,
               correct_arg_types,
               lhs_type.as_roland_type_info()
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_arg_types, rhs_type) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Binary operator {:?} requires RHS to have type matching {:?}; instead got {}",
               bin_op,
               correct_arg_types,
               rhs_type.as_roland_type_info()
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else if lhs_type != rhs_type {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Binary operator {:?} requires LHS and RHS to have identical type; instead got {} and {}",
               bin_op,
               lhs_type.as_roland_type_info(),
               rhs_type.as_roland_type_info()
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else {
            match bin_op {
               BinOp::Add
               | BinOp::Subtract
               | BinOp::Multiply
               | BinOp::Divide
               | BinOp::BitwiseAnd
               | BinOp::BitwiseOr
               | BinOp::BitwiseXor => lhs_type.clone(),
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
         do_type(err_stream, e, validation_context);

         let (correct_type, node_type): (&[TypeValidator], _) = match un_op {
            UnOp::Dereference => {
               let mut new_type = e.exp_type.clone().unwrap();
               // If this fails, it will be caught by the type matcher
               let _ = new_type.decrement_indirection_count();
               (&[TypeValidator::AnyPointer], new_type)
            }
            UnOp::Negate => (&[TypeValidator::AnyInt], e.exp_type.clone().unwrap()),
            UnOp::Complement => (
               &[TypeValidator::Bool, TypeValidator::AnyInt],
               e.exp_type.clone().unwrap(),
            ),
            UnOp::AddressOf => {
               let mut new_type = e.exp_type.clone().unwrap();
               new_type.increment_indirection_count();
               (&[TypeValidator::Any], new_type)
            }
         };

         let result_type = if e.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::CompileError) {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_type, e.exp_type.as_ref().unwrap()) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Expected type {:?} for expression {:?}; instead got {}",
               correct_type,
               un_op,
               e.exp_type.as_ref().unwrap().as_roland_type_info()
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::AddressOf && !e.expression.is_lvalue() {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "A pointer can only be taken to a value that resides in memory; i.e. a variable or parameter"
            )
            .unwrap();
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
               writeln!(err_stream, "Encountered undefined variable `{}`", id).unwrap();
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::ProcedureCall(name, args) => {
         for arg in args.iter_mut() {
            do_type(err_stream, arg, validation_context);
         }

         if name == "main" {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "`main` is a special procedure and is not allowed to be called"
            )
            .unwrap();
         }

         match validation_context.procedure_info.get(name) {
            Some(procedure_info) => {
               expr_node.exp_type = Some(procedure_info.ret_type.clone());

               if validation_context.cur_procedure_info.unwrap().pure && !procedure_info.pure {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "Encountered call to procedure `{}` (impure) in func (pure)",
                     name
                  )
                  .unwrap();
               }

               if procedure_info.parameters.len() != args.len() {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "In call to `{}`, mismatched arity. Expected {} arguments but got {}",
                     name,
                     procedure_info.parameters.len(),
                     args.len()
                  )
                  .unwrap();
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
                        writeln!(
                           err_stream,
                           "In call to `{}`, encountered argument of type {} when we expected {}",
                           name,
                           actual_type.as_roland_type_info(),
                           expected.as_roland_type_info()
                        )
                        .unwrap();
                     }
                  }
               }
            }
            None => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Encountered call to undefined procedure/function `{}`",
                  name
               )
               .unwrap();
               expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
            }
         }
      }
      Expression::StructLiteral(struct_name, fields) => {
         for field in fields.iter_mut() {
            do_type(err_stream, &mut field.1, validation_context);
         }

         match validation_context.struct_info.get(struct_name) {
            Some(defined_struct) => {
               // TODO, interning...
               expr_node.exp_type = Some(ExpressionType::Value(ValueType::Struct(struct_name.clone())));

               let defined_fields = &defined_struct.field_types;

               let mut unmatched_fields: HashSet<&str> = defined_fields.keys().map(|x| x.as_str()).collect();
               for field in fields {
                  // Extraneous field check
                  let defined_type = match defined_fields.get(&field.0) {
                     Some(x) => x,
                     None => {
                        validation_context.error_count += 1;
                        writeln!(
                           err_stream,
                           "`{}` is not a known field of struct `{}`",
                           field.0, struct_name,
                        )
                        .unwrap();
                        writeln!(err_stream, "↳ struct defined @ line {}, column {}", defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col).unwrap();
                        continue;
                     }
                  };

                  // Duplicate field check
                  if !unmatched_fields.remove(field.0.as_str()) {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "`{}` is a valid field of struct `{}`, but is duplicated",
                        field.0, struct_name,
                     )
                     .unwrap();
                     writeln!(err_stream, "↳ struct defined @ line {}, column {}", defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col).unwrap();
                  }

                  // Type validation
                  if defined_type.is_any_known_int()
                     && field.1.exp_type.as_ref().unwrap() == &ExpressionType::Value(ValueType::UnknownInt)
                  {
                     set_inferred_type(defined_type.clone(), &mut field.1, validation_context);
                  } else if field.1.exp_type.as_ref().unwrap() != defined_type {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "For field `{}` of struct `{}`, encountered value of type {} when we expected {}",
                        field.0,
                        struct_name,
                        field.1.exp_type.as_ref().unwrap().as_roland_type_info(),
                        defined_type.as_roland_type_info(),
                     )
                     .unwrap();
                     writeln!(err_stream, "↳ struct defined @ line {}, column {}", defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col).unwrap();
                  }
               }
               // Missing field check
               if !unmatched_fields.is_empty() {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "Literal of struct `{}` is missing fields {:?}",
                     struct_name, unmatched_fields,
                  )
                  .unwrap();
                  writeln!(err_stream, "↳ struct defined @ line {}, column {}", defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col).unwrap();
               }
            }
            None => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Encountered construction of undefined struct `{}`",
                  struct_name
               )
               .unwrap();
               expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
            }
         }
      }
      Expression::FieldAccess(fields, lhs) => {
         do_type(err_stream, lhs, validation_context);

         if let Some(ExpressionType::Value(ValueType::Struct(base_struct_name))) = lhs.exp_type.as_ref() {
            let mut current_struct = base_struct_name.as_str();
            let mut current_struct_info = &validation_context.struct_info.get(current_struct).unwrap().field_types;
            for (field, next_field) in fields.iter().take(fields.len() - 1).zip(fields.iter().skip(1)) {
               match current_struct_info.get(field) {
                  Some(ExpressionType::Value(ValueType::Struct(x))) => {
                     current_struct = x.as_str();
                     current_struct_info = &validation_context.struct_info.get(current_struct).unwrap().field_types;
                  }
                  Some(_) => {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "Field `{}` is not a struct type and so doesn't have field `{}`",
                        field, next_field,
                     )
                     .unwrap();
                     expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
                     break;
                  }
                  None => {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "Struct `{}` does not have a field `{}`",
                        current_struct, field,
                     )
                     .unwrap();
                     expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
                     break;
                  }
               }
            }

            if expr_node.exp_type != Some(ExpressionType::Value(ValueType::CompileError)) {
               match current_struct_info.get(fields.last().unwrap()) {
                  Some(e_type) => {
                     expr_node.exp_type = Some(e_type.clone());
                  }
                  None => {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "Struct `{}` does not have a field `{}`",
                        current_struct,
                        fields.last().unwrap(),
                     )
                     .unwrap();
                     expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
                  }
               }
            }
         } else {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Encountered field access on type {}; only structs have fields",
               lhs.exp_type.as_ref().unwrap().as_roland_type_info()
            )
            .unwrap();
            expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
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
      Expression::UnitLiteral => unreachable!(),
      Expression::Variable(_) => unreachable!(),
      Expression::ProcedureCall(_, _) => unreachable!(),
      Expression::StructLiteral(_, _) => unreachable!(),
      Expression::FieldAccess(_, _) => unreachable!(),
   }
}
