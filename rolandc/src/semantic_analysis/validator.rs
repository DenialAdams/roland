use super::type_inference::try_set_inferred_type;
use super::{ProcedureInfo, StaticInfo, StructInfo, ValidationContext};
use crate::interner::{Interner, StrId};
use crate::lex::SourceInfo;
use crate::parse::{BinOp, BlockNode, Expression, ExpressionNode, Program, Statement, StatementNode, UnOp};
use crate::type_data::{ExpressionType, IntWidth, ValueType, I32_TYPE, U32_TYPE};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};
use std::io::Write;

#[derive(Debug)]
enum TypeValidator {
   Bool,
   AnyInt,
   AnyFloat,
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
      (TypeValidator::AnyFloat, ExpressionType::Value(ValueType::Float(_))) => true,
      (TypeValidator::AnyFloat, ExpressionType::Value(ValueType::UnknownFloat)) => true,
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

fn recursive_struct_check(
   base_name: StrId,
   struct_fields: &IndexMap<StrId, ExpressionType>,
   struct_info: &IndexMap<StrId, StructInfo>,
) -> bool {
   let mut is_recursive = false;

   for struct_field in struct_fields.iter().flat_map(|x| match &x.1 {
      ExpressionType::Value(ValueType::Struct(x)) => Some(*x),
      _ => None,
   }) {
      if struct_field == base_name {
         is_recursive = true;
         break;
      }

      is_recursive |= struct_info
         .get(&struct_field)
         .map(|si| recursive_struct_check(base_name, &si.field_types, struct_info))
         .unwrap_or(false);
   }

   is_recursive
}

pub fn type_and_check_validity<W: Write>(program: &mut Program, err_stream: &mut W, interner: &mut Interner) -> u64 {
   let mut procedure_info: IndexMap<StrId, ProcedureInfo> = IndexMap::new();
   let mut struct_info: IndexMap<StrId, StructInfo> = IndexMap::new();
   let mut static_info: IndexMap<StrId, StaticInfo> = IndexMap::new();
   let mut error_count = 0;

   // Built-In functions
   let standard_lib_procs = [
      (
         interner.intern("wasm_memory_size"),
         false,
         vec![],
         ExpressionType::Value(I32_TYPE),
      ),
      (
         interner.intern("wasm_memory_grow"),
         false,
         vec![ExpressionType::Value(I32_TYPE)],
         ExpressionType::Value(I32_TYPE),
      ),
      (
         interner.intern("fd_write"),
         false,
         vec![
            ExpressionType::Value(I32_TYPE),
            ExpressionType::Value(I32_TYPE),
            ExpressionType::Value(I32_TYPE),
            ExpressionType::Value(I32_TYPE),
         ],
         ExpressionType::Value(I32_TYPE),
      ),
   ];
   for p in standard_lib_procs.iter() {
      procedure_info.insert(
         p.0,
         ProcedureInfo {
            pure: p.1,
            parameters: p.2.clone(),
            named_parameters: HashMap::new(),
            ret_type: p.3.clone(),
            procedure_begin_location: SourceInfo { line: 0, col: 0 },
         },
      );
   }

   let mut parameter_dupe_check = HashSet::new();
   for procedure in program.procedures.iter_mut() {
      parameter_dupe_check.clear();
      parameter_dupe_check.reserve(procedure.parameters.len());

      let mut first_named_param = None;
      let mut reported_named_error = false;
      for (i, param) in procedure.parameters.iter().enumerate() {
         if !parameter_dupe_check.insert(param.name) {
            error_count += 1;
            writeln!(
               err_stream,
               "Procedure/function `{}` has a duplicate parameter `{}`",
               interner.lookup(procedure.name),
               interner.lookup(param.name),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ procedure/function defined @ line {}, column {}",
               procedure.procedure_begin_location.line, procedure.procedure_begin_location.col
            )
            .unwrap();
         }

         if param.named && first_named_param.is_none() {
            first_named_param = Some(i);
         }

         if !param.named && first_named_param.is_some() && !reported_named_error {
            reported_named_error = true;
            error_count += 1;
            writeln!(
               err_stream,
               "Procedure/function `{}` has named parameter(s) which come before non-named parameter(s)",
               interner.lookup(procedure.name),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ procedure/function defined @ line {}, column {}",
               procedure.procedure_begin_location.line, procedure.procedure_begin_location.col
            )
            .unwrap();
         }
      }

      if !reported_named_error && first_named_param.is_some() {
         // It doesn't really matter how we sort these, as long as we do it consistently for arguments
         // AND that there are no equal elements (in this case, we already check that parameters don't have the same name)
         procedure.parameters[first_named_param.unwrap()..].sort_by_key(|x| x.name);
      }

      match procedure_info.insert(
         procedure.name,
         ProcedureInfo {
            pure: procedure.pure,
            parameters: procedure.parameters.iter().map(|x| x.p_type.clone()).collect(),
            named_parameters: procedure.parameters.iter().filter(|x| x.named).map(|x| (x.name, x.p_type.clone())).collect(),
            ret_type: procedure.ret_type.clone(),
            procedure_begin_location: procedure.procedure_begin_location,
         },
      ) {
         Some(old_procedure) => {
            error_count += 1;
            let procedure_name_str = interner.lookup(procedure.name);
            writeln!(
               err_stream,
               "Encountered duplicate procedures/functions with the same name `{}`",
               procedure_name_str
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ first procedure/function defined @ line {}, column {}",
               old_procedure.procedure_begin_location.line, old_procedure.procedure_begin_location.col
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ second procedure/function defined @ line {}, column {}",
               procedure.procedure_begin_location.line, procedure.procedure_begin_location.col
            )
            .unwrap();
         }
         None => (),
      }
   }

   for a_struct in program.structs.iter() {
      let mut field_map = IndexMap::with_capacity(a_struct.fields.len());
      for field in a_struct.fields.iter() {
         match field_map.insert(field.0.clone(), field.1.clone()) {
            Some(__) => {
               error_count += 1;
               writeln!(
                  err_stream,
                  "Struct `{}` has a duplicate field `{}`",
                  interner.lookup(a_struct.name),
                  interner.lookup(field.0),
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ struct defined @ line {}, column {}",
                  a_struct.struct_begin_location.line, a_struct.struct_begin_location.col
               )
               .unwrap();
            }
            None => (),
         }
      }

      match struct_info.insert(
         a_struct.name.clone(),
         StructInfo {
            field_types: field_map,
            struct_begin_location: a_struct.struct_begin_location,
         },
      ) {
         Some(old_struct) => {
            error_count += 1;
            writeln!(
               err_stream,
               "Encountered duplicate structs with the same name `{}`",
               interner.lookup(a_struct.name)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ first struct defined @ line {}, column {}",
               old_struct.struct_begin_location.line, old_struct.struct_begin_location.col
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ second struct defined @ line {}, column {}",
               a_struct.struct_begin_location.line, a_struct.struct_begin_location.col
            )
            .unwrap();
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
         let etype_str = e_type.as_roland_type_info(interner);
         writeln!(
            err_stream,
            "Field `{}` of struct `{}` is of undeclared type `{}`",
            interner.lookup(*field),
            interner.lookup(*struct_i.0),
            etype_str,
         )
         .unwrap();
         writeln!(
            err_stream,
            "↳ struct defined @ line {}, column {}",
            struct_i.1.struct_begin_location.line, struct_i.1.struct_begin_location.col
         )
         .unwrap();
      }

      if recursive_struct_check(*struct_i.0, &struct_i.1.field_types, &struct_info) {
         error_count += 1;
         writeln!(
            err_stream,
            "Struct `{}` contains itself, which isn't allowed as it would result in an infinitely large struct",
            interner.lookup(*struct_i.0),
         )
         .unwrap();
         writeln!(
            err_stream,
            "↳ struct defined @ line {}, column {}",
            struct_i.1.struct_begin_location.line, struct_i.1.struct_begin_location.col
         )
         .unwrap();
      }
   }

   for static_node in program.statics.iter() {
      let static_type = &static_node.static_type;
      let si = &static_node.static_begin_location;

      if match static_type {
         ExpressionType::Value(ValueType::Struct(s)) => struct_info.get(s).is_none(),
         _ => false,
      } {
         error_count += 1;
         let static_type_str = static_type.as_roland_type_info(interner);
         writeln!(
            err_stream,
            "Static `{}` is of undeclared type `{}`",
            interner.lookup(static_node.name),
            static_type_str,
         )
         .unwrap();
         writeln!(err_stream, "↳ static defined @ line {}, column {}", si.line, si.col).unwrap();
      }

      match static_info.insert(
         static_node.name.clone(),
         StaticInfo {
            static_type: static_node.static_type.clone(),
            static_begin_location: static_node.static_begin_location,
         },
      ) {
         Some(old_static) => {
            error_count += 1;
            writeln!(
               err_stream,
               "Encountered duplicate statics with the same name `{}`",
               interner.lookup(static_node.name),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ first static defined @ line {}, column {}",
               old_static.static_begin_location.line, old_static.static_begin_location.col
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ second static defined @ line {}, column {}",
               static_node.static_begin_location.line, static_node.static_begin_location.col
            )
            .unwrap();
         }
         None => (),
      }
   }

   let mut validation_context = ValidationContext {
      string_literals: HashSet::new(),
      variable_types: HashMap::new(),
      error_count,
      procedure_info: &procedure_info,
      struct_info: &struct_info,
      static_info: &static_info,
      cur_procedure_info: None,
      block_depth: 0,
      loop_depth: 0,
      unknown_ints: 0,
      unknown_floats: 0,
   };

   let main_token = interner.intern("main");
   if !validation_context.procedure_info.contains_key(&main_token) {
      validation_context.error_count += 1;
      writeln!(err_stream, "A procedure with the name `main` must be present").unwrap();
   } else if validation_context.procedure_info.get(&main_token).unwrap().ret_type
      != ExpressionType::Value(ValueType::Unit)
   {
      validation_context.error_count += 1;
      writeln!(
         err_stream,
         "`main` is a special procedure and is not allowed to return a value"
      )
      .unwrap();
      let si = validation_context
         .procedure_info
         .get(&main_token)
         .unwrap()
         .procedure_begin_location;
      writeln!(err_stream, "↳ main defined @ line {}, column {}", si.line, si.col).unwrap();
   }

   // We won't proceed with type checking because there could be false positives due to
   // procedure/struct definition errors.
   if validation_context.error_count > 0 {
      return validation_context.error_count;
   }

   for procedure in program.procedures.iter_mut() {
      validation_context.variable_types.clear();
      validation_context.cur_procedure_info = procedure_info.get(&procedure.name);

      for parameter in procedure.parameters.iter() {
         validation_context
            .variable_types
            .insert(parameter.name, (parameter.p_type.clone(), 0));
         procedure.locals.insert(parameter.name, parameter.p_type.clone());
      }

      type_block(
         err_stream,
         &mut procedure.block,
         &mut validation_context,
         &mut procedure.locals,
         interner,
      );

      // Ensure that the last statement is a return statement
      // (it has already been type checked, so we don't have to check that)
      match (
         &procedure.ret_type,
         procedure.block.statements.last().map(|x| &x.statement),
      ) {
         (ExpressionType::Value(ValueType::Unit), _) => (),
         (_, Some(Statement::ReturnStatement(_))) => (),
         (x, _) => {
            validation_context.error_count += 1;
            let x_str = x.as_roland_type_info(interner);
            writeln!(
               err_stream,
               "Procedure/function `{}` is declared to return type {} but is missing a final return statement",
               interner.lookup(procedure.name),
               x_str,
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ procedure/function defined @ line {}, column {}",
               procedure.procedure_begin_location.line, procedure.procedure_begin_location.col
            )
            .unwrap();
            if let Some(fs) = procedure.block.statements.last() {
               writeln!(
                  err_stream,
                  "↳ actual final statement @ line {}, column {}",
                  fs.statement_begin_location.line, fs.statement_begin_location.col
               )
               .unwrap();
            }
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

   if validation_context.unknown_floats > 0 {
      validation_context.error_count += 1;
      writeln!(
         err_stream,
         "We weren't able to determine the types of {} float literals",
         validation_context.unknown_floats
      )
      .unwrap();
   }

   let err_count = validation_context.error_count;
   program.literals = validation_context.string_literals;
   program.struct_info = struct_info;
   program.static_info = static_info;

   err_count
}

fn type_statement<W: Write>(
   err_stream: &mut W,
   statement: &mut StatementNode,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut IndexMap<StrId, ExpressionType>,
   interner: &mut Interner,
) {
   match &mut statement.statement {
      Statement::AssignmentStatement(len, en) => {
         do_type(err_stream, len, validation_context, interner);
         do_type(err_stream, en, validation_context, interner);

         try_set_inferred_type(
            len.exp_type.as_ref().unwrap(),
            en,
            validation_context,
            err_stream,
            interner,
         );

         let lhs_type = len.exp_type.as_ref().unwrap();
         let rhs_type = en.exp_type.as_ref().unwrap();

         if lhs_type == &ExpressionType::Value(ValueType::CompileError)
            || rhs_type == &ExpressionType::Value(ValueType::CompileError)
         {
            // avoid cascading errors
         } else if lhs_type != rhs_type && lhs_type.is_concrete_type() && rhs_type.is_concrete_type() {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Left hand side of assignment has type {} which does not match the type of the right hand side {}",
               lhs_type.as_roland_type_info(interner),
               rhs_type.as_roland_type_info(interner),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ left hand side @ line {}, column {}",
               len.expression_begin_location.line, len.expression_begin_location.col
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ right hand side @ line {}, column {}",
               en.expression_begin_location.line, en.expression_begin_location.col
            )
            .unwrap();
         } else if !len.expression.is_lvalue() {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Left hand side of assignment is not a valid memory location; i.e. a variable, field, or parameter"
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               len.expression_begin_location.line, len.expression_begin_location.col
            )
            .unwrap();
         }
      }
      Statement::BlockStatement(bn) => {
         type_block(err_stream, bn, validation_context, cur_procedure_locals, interner);
      }
      Statement::ContinueStatement => {
         if validation_context.loop_depth == 0 {
            validation_context.error_count += 1;
            writeln!(err_stream, "Continue statement can only be used in a loop").unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               statement.statement_begin_location.line, statement.statement_begin_location.col
            )
            .unwrap();
         }
      }
      Statement::BreakStatement => {
         if validation_context.loop_depth == 0 {
            validation_context.error_count += 1;
            writeln!(err_stream, "Break statement can only be used in a loop").unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               statement.statement_begin_location.line, statement.statement_begin_location.col
            )
            .unwrap();
         }
      }
      Statement::LoopStatement(bn) => {
         validation_context.loop_depth += 1;
         type_block(err_stream, bn, validation_context, cur_procedure_locals, interner);
         validation_context.loop_depth -= 1;
      }
      Statement::ExpressionStatement(en) => {
         do_type(err_stream, en, validation_context, interner);
      }
      Statement::IfElseStatement(en, block_1, block_2) => {
         type_block(err_stream, block_1, validation_context, cur_procedure_locals, interner);
         type_statement(err_stream, block_2, validation_context, cur_procedure_locals, interner);
         do_type(err_stream, en, validation_context, interner);
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if if_exp_type != &ExpressionType::Value(ValueType::Bool)
            && if_exp_type != &ExpressionType::Value(ValueType::CompileError)
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Value of if expression must be a bool; instead got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               en.expression_begin_location.line, en.expression_begin_location.col
            )
            .unwrap();
         }
      }
      Statement::ReturnStatement(en) => {
         do_type(err_stream, en, validation_context, interner);
         let cur_procedure_info = validation_context.cur_procedure_info.unwrap();

         // Type Inference
         try_set_inferred_type(
            &cur_procedure_info.ret_type,
            en,
            validation_context,
            err_stream,
            interner,
         );

         if en.exp_type.as_ref().unwrap().is_concrete_type()
            && en.exp_type.as_ref().unwrap() != &cur_procedure_info.ret_type
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Value of return statement must match declared return type {}; got {}",
               cur_procedure_info.ret_type.as_roland_type_info(interner),
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               en.expression_begin_location.line, en.expression_begin_location.col
            )
            .unwrap();
         }
      }
      Statement::VariableDeclaration(id, en, dt) => {
         do_type(err_stream, en, validation_context, interner);

         if let Some(v) = dt.as_ref() {
            try_set_inferred_type(v, en, validation_context, err_stream, interner);
         }

         let result_type = if dt.is_some() && *dt != en.exp_type && en.exp_type.as_ref().unwrap().is_concrete_type() {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Declared type {} does not match actual expression type {}",
               dt.as_ref().unwrap().as_roland_type_info(interner),
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ declaration @ line {}, column {}",
               statement.statement_begin_location.line, statement.statement_begin_location.col
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ expression @ line {}, column {}",
               en.expression_begin_location.line, en.expression_begin_location.col
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
            let dt_str = dt.as_ref().unwrap().as_roland_type_info(interner);
            writeln!(
               err_stream,
               "Variable `{}` is declared with undefined type `{}`",
               interner.lookup(*id),
               dt_str,
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ declaration @ line {}, column {}",
               statement.statement_begin_location.line, statement.statement_begin_location.col
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else {
            en.exp_type.clone().unwrap()
         };

         if validation_context.static_info.contains_key(id) || validation_context.variable_types.contains_key(id) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Variable shadowing is not supported at this time (`{}`)",
               interner.lookup(*id)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               statement.statement_begin_location.line, statement.statement_begin_location.col
            )
            .unwrap();
         } else {
            validation_context
               .variable_types
               .insert(*id, (en.exp_type.clone().unwrap(), validation_context.block_depth));
            cur_procedure_locals.insert(*id, result_type);
         }
      }
   }
}

fn type_block<W: Write>(
   err_stream: &mut W,
   bn: &mut BlockNode,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut IndexMap<StrId, ExpressionType>,
   interner: &mut Interner,
) {
   validation_context.block_depth += 1;

   for statement in bn.statements.iter_mut() {
      type_statement(
         err_stream,
         statement,
         validation_context,
         cur_procedure_locals,
         interner,
      );
   }

   validation_context.block_depth -= 1;
   let cur_block_depth = validation_context.block_depth;
   validation_context.variable_types.retain(|_, v| v.1 <= cur_block_depth);
}

fn do_type<W: Write>(
   err_stream: &mut W,
   expr_node: &mut ExpressionNode,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) {
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
      Expression::FloatLiteral(_) => {
         validation_context.unknown_floats += 1;
         expr_node.exp_type = Some(ExpressionType::Value(ValueType::UnknownFloat));
      }
      Expression::StringLiteral(lit) => {
         validation_context.string_literals.insert(*lit);
         expr_node.exp_type = Some(ExpressionType::Value(ValueType::Struct(interner.intern("String"))));
      }
      Expression::Extend(target_type, e) => {
         do_type(err_stream, e, validation_context, interner);

         let e_type = e.exp_type.as_ref().unwrap();

         let result_type = if !e_type.is_concrete_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else {
            let valid_cast = match (e_type, &target_type) {
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                  x.width < y.width
               }
               (ExpressionType::Value(ValueType::Bool), ExpressionType::Value(ValueType::Int(_))) => true,
               _ => false,
            };

            if valid_cast {
               target_type.clone()
            } else {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Extend encountered an operand of type {} which can not be extended to type {}",
                  e_type.as_roland_type_info(interner),
                  target_type.as_roland_type_info(interner),
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ extend @ line {}, column {}",
                  expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ operand @ line {}, column {}",
                  e.expression_begin_location.line, e.expression_begin_location.col
               )
               .unwrap();
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::Transmute(target_type, e) => {
         do_type(err_stream, e, validation_context, interner);

         if target_type.is_pointer() {
            // todo: hardcoded pointer size
            try_set_inferred_type(
               &ExpressionType::Value(U32_TYPE),
               e,
               validation_context,
               err_stream,
               interner,
            );
         }

         let e_type = e.exp_type.as_ref().unwrap();

         let result_type = if !e_type.is_concrete_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else {
            let valid_cast = match (e_type, &target_type) {
               // TODO: pointer width is hardcoded
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Pointer(_, _))
                  if x.width == IntWidth::Four =>
               {
                  true
               }
               (ExpressionType::Pointer(_, _), ExpressionType::Value(ValueType::Int(x)))
                  if x.width == IntWidth::Four =>
               {
                  true
               }
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                  x.width == y.width
               }
               _ => false,
            };

            if valid_cast {
               target_type.clone()
            } else {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Transmute encountered an operand of type {} which can not be transmuted to type {}",
                  e_type.as_roland_type_info(interner),
                  target_type.as_roland_type_info(interner),
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ transmute @ line {}, column {}",
                  expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ operand @ line {}, column {}",
                  e.expression_begin_location.line, e.expression_begin_location.col
               )
               .unwrap();
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::Truncate(target_type, e) => {
         do_type(err_stream, e, validation_context, interner);

         let e_type = e.exp_type.as_ref().unwrap();

         let result_type = if !e_type.is_concrete_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else {
            let valid_cast = match (e_type, &target_type) {
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                  x.width > y.width
               }
               _ => false,
            };

            if valid_cast {
               target_type.clone()
            } else {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Truncate encountered an operand of type {} which can not be truncated to type {}",
                  e_type.as_roland_type_info(interner),
                  target_type.as_roland_type_info(interner),
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ truncate @ line {}, column {}",
                  expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ operand @ line {}, column {}",
                  e.expression_begin_location.line, e.expression_begin_location.col
               )
               .unwrap();
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::BinaryOperator(bin_op, e) => {
         do_type(err_stream, &mut e.0, validation_context, interner);
         do_type(err_stream, &mut e.1, validation_context, interner);

         let correct_arg_types: &[TypeValidator] = match bin_op {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::Remainder
            | BinOp::GreaterThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThan
            | BinOp::LessThanOrEqualTo => &[TypeValidator::AnyInt, TypeValidator::AnyFloat],
            BinOp::Equality | BinOp::NotEquality | BinOp::BitwiseAnd | BinOp::BitwiseOr | BinOp::BitwiseXor => {
               &[TypeValidator::AnyInt, TypeValidator::Bool]
            }
         };

         try_set_inferred_type(
            e.0.exp_type.as_ref().unwrap(),
            &mut e.1,
            validation_context,
            err_stream,
            interner,
         );
         try_set_inferred_type(
            e.1.exp_type.as_ref().unwrap(),
            &mut e.0,
            validation_context,
            err_stream,
            interner,
         );

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
               lhs_type.as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               e.0.expression_begin_location.line, e.0.expression_begin_location.col
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
               rhs_type.as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               e.1.expression_begin_location.line, e.1.expression_begin_location.col
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else if lhs_type != rhs_type && lhs_type.is_concrete_type() && rhs_type.is_concrete_type() {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Binary operator {:?} requires LHS and RHS to have identical type; instead got {} and {}",
               bin_op,
               lhs_type.as_roland_type_info(interner),
               rhs_type.as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ left hand side @ line {}, column {}",
               e.0.expression_begin_location.line, e.0.expression_begin_location.col
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ right hand side @ line {}, column {}",
               e.1.expression_begin_location.line, e.1.expression_begin_location.col
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else {
            match bin_op {
               BinOp::Add
               | BinOp::Subtract
               | BinOp::Multiply
               | BinOp::Divide
               | BinOp::Remainder
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
         do_type(err_stream, e, validation_context, interner);

         let (correct_type, node_type): (&[TypeValidator], _) = match un_op {
            UnOp::Dereference => {
               let mut new_type = e.exp_type.clone().unwrap();
               // If this fails, it will be caught by the type matcher
               let _ = new_type.decrement_indirection_count();
               (&[TypeValidator::AnyPointer], new_type)
            }
            UnOp::Negate => (
               &[TypeValidator::AnyInt, TypeValidator::AnyFloat],
               e.exp_type.clone().unwrap(),
            ),
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
               e.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               e.expression_begin_location.line, e.expression_begin_location.col
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
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
            )
            .unwrap();
            ExpressionType::Value(ValueType::CompileError)
         } else {
            node_type
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::Variable(id) => {
         let defined_type = validation_context
            .static_info
            .get(id)
            .map(|x| &x.static_type)
            .or_else(|| validation_context.variable_types.get(id).map(|x| &x.0));

         let result_type = match defined_type {
            Some(t) => t.clone(),
            None => {
               validation_context.error_count += 1;
               writeln!(err_stream, "Encountered undefined variable `{}`", interner.lookup(*id)).unwrap();
               writeln!(
                  err_stream,
                  "↳ line {}, column {}",
                  expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
               )
               .unwrap();
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         expr_node.exp_type = Some(result_type);
      }
      Expression::ProcedureCall(name, args) => {
         for arg in args.iter_mut() {
            do_type(err_stream, &mut arg.expr, validation_context, interner);
         }

         if *name == interner.intern("main") {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "`main` is a special procedure and is not allowed to be called"
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
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
                     interner.lookup(*name)
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ line {}, column {}",
                     expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                  )
                  .unwrap();
               }

               // Validate that there are no non-named arguments after named arguments, then reorder the argument list
               let first_named_arg = args.iter().enumerate().find(|(_, arg)| arg.name.is_some()).map(|x| x.0);
               let last_normal_arg = args.iter().enumerate().rfind(|(_, arg)| arg.name.is_none()).map(|x| x.0);
               let args_in_order = first_named_arg.and_then(|x| last_normal_arg.and_then(|y| Some(x > y))).unwrap_or(true);

               if !args_in_order {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "Call to `{}` has named argument(s) which come before non-named argument(s)",
                     interner.lookup(*name),
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ line {}, column {}",
                     expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                  )
                  .unwrap();
               } else if let Some(i) = first_named_arg {
                  args[i..].sort_by_key(|x| x.name);
               }

               if args_in_order && procedure_info.parameters.len() != args.len() {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "In call to `{}`, mismatched arity. Expected {} arguments but got {}",
                     interner.lookup(*name),
                     procedure_info.parameters.len(),
                     args.len()
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ line {}, column {}",
                     expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                  )
                  .unwrap();
               // We shortcircuit here, because there will likely be lots of mistmatched types if an arg was forgotten
               } else if args_in_order {
                  let expected_types = procedure_info.parameters.iter();
                  for (actual, expected) in args.iter_mut().zip(expected_types) {
                     // These should be at the end by now, so we've checked everything we needed to
                     if actual.name.is_some() {
                        break;
                     }

                     try_set_inferred_type(expected, &mut actual.expr, validation_context, err_stream, interner);

                     let actual_type = actual.expr.exp_type.as_ref().unwrap();
                     if actual_type != expected && *actual_type != ExpressionType::Value(ValueType::CompileError) {
                        validation_context.error_count += 1;
                        let actual_type_str = actual_type.as_roland_type_info(interner);
                        let expected_type_str = expected.as_roland_type_info(interner);
                        writeln!(
                           err_stream,
                           "In call to `{}`, encountered argument of type {} when we expected {}",
                           interner.lookup(*name),
                           actual_type_str,
                           expected_type_str,
                        )
                        .unwrap();
                        writeln!(
                           err_stream,
                           "↳ line {}, column {}",
                           expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                        )
                        .unwrap();
                     }
                  }

                  for arg in args.iter_mut().filter(|x| x.name.is_some()) {
                     let expected = procedure_info.named_parameters.get(&arg.name.unwrap());
                     
                     if expected.is_none() {
                        validation_context.error_count += 1;
                        writeln!(
                           err_stream,
                           "In call to `{}`, encountered named argument `{}` that does not correspond to any named parameter",
                           interner.lookup(*name),
                           interner.lookup(arg.name.unwrap()),
                        )
                        .unwrap();
                        writeln!(
                           err_stream,
                           "↳ line {}, column {}",
                           expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                        )
                        .unwrap();
                        continue;
                     }

                     let expected = expected.unwrap();

                     try_set_inferred_type(expected, &mut arg.expr, validation_context, err_stream, interner);

                     let actual_type = arg.expr.exp_type.as_ref().unwrap();
                     if actual_type != expected && *actual_type != ExpressionType::Value(ValueType::CompileError) {
                        validation_context.error_count += 1;
                        let actual_type_str = actual_type.as_roland_type_info(interner);
                        let expected_type_str = expected.as_roland_type_info(interner);
                        writeln!(
                           err_stream,
                           "In call to `{}`, encountered argument of type {} when we expected {} for named parameter {}",
                           interner.lookup(*name),
                           actual_type_str,
                           expected_type_str,
                           interner.lookup(arg.name.unwrap())
                        )
                        .unwrap();
                        writeln!(
                           err_stream,
                           "↳ line {}, column {}",
                           expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
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
                  interner.lookup(*name),
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ line {}, column {}",
                  expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
               )
               .unwrap();
               expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
            }
         }
      }
      Expression::StructLiteral(struct_name, fields) => {
         for field in fields.iter_mut() {
            do_type(err_stream, &mut field.1, validation_context, interner);
         }

         match validation_context.struct_info.get(struct_name) {
            Some(defined_struct) => {
               expr_node.exp_type = Some(ExpressionType::Value(ValueType::Struct(*struct_name)));

               let defined_fields = &defined_struct.field_types;

               let mut unmatched_fields: HashSet<StrId> = defined_fields.keys().copied().collect();
               for field in fields {
                  // Extraneous field check
                  let defined_type = match defined_fields.get(&field.0) {
                     Some(x) => x,
                     None => {
                        validation_context.error_count += 1;
                        writeln!(
                           err_stream,
                           "`{}` is not a known field of struct `{}`",
                           interner.lookup(field.0),
                           interner.lookup(*struct_name),
                        )
                        .unwrap();
                        writeln!(
                           err_stream,
                           "↳ struct defined @ line {}, column {}",
                           defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col
                        )
                        .unwrap();
                        writeln!(
                           err_stream,
                           "↳ struct instantiated @ line {}, column {}",
                           expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                        )
                        .unwrap();
                        continue;
                     }
                  };

                  // Duplicate field check
                  if !unmatched_fields.remove(&field.0) {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "`{}` is a valid field of struct `{}`, but is duplicated",
                        interner.lookup(field.0),
                        interner.lookup(*struct_name),
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ struct defined @ line {}, column {}",
                        defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ struct instantiated @ line {}, column {}",
                        expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                     )
                     .unwrap();
                  }

                  try_set_inferred_type(defined_type, &mut field.1, validation_context, err_stream, interner);

                  if field.1.exp_type.as_ref().unwrap() != defined_type
                     && field.1.exp_type.as_ref().unwrap().is_concrete_type()
                  {
                     validation_context.error_count += 1;
                     let field_1_type_str = field.1.exp_type.as_ref().unwrap().as_roland_type_info(interner);
                     let defined_type_str = defined_type.as_roland_type_info(interner);
                     writeln!(
                        err_stream,
                        "For field `{}` of struct `{}`, encountered value of type {} when we expected {}",
                        interner.lookup(field.0),
                        interner.lookup(*struct_name),
                        field_1_type_str,
                        defined_type_str,
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ struct defined @ line {}, column {}",
                        defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ struct instantiated @ line {}, column {}",
                        expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ field value @ line {}, column {}",
                        field.1.expression_begin_location.line, field.1.expression_begin_location.col
                     )
                     .unwrap();
                  }
               }
               // Missing field check
               if !unmatched_fields.is_empty() {
                  validation_context.error_count += 1;
                  let unmatched_fields_str: Vec<&str> = unmatched_fields.iter().map(|x| interner.lookup(*x)).collect();
                  writeln!(
                     err_stream,
                     "Literal of struct `{}` is missing fields [{}]",
                     interner.lookup(*struct_name),
                     unmatched_fields_str.join(", "),
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ struct defined @ line {}, column {}",
                     defined_struct.struct_begin_location.line, defined_struct.struct_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ struct instantiated @ line {}, column {}",
                     expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
                  )
                  .unwrap();
               }
            }
            None => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Encountered construction of undefined struct `{}`",
                  interner.lookup(*struct_name)
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ line {}, column {}",
                  expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
               )
               .unwrap();
               expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
            }
         }
      }
      Expression::FieldAccess(fields, lhs) => {
         do_type(err_stream, lhs, validation_context, interner);

         if let Some(ExpressionType::Value(ValueType::Struct(base_struct_name))) = lhs.exp_type.as_ref() {
            let mut current_struct = *base_struct_name;
            let mut current_struct_info = &validation_context.struct_info.get(&current_struct).unwrap().field_types;
            for (field, next_field) in fields.iter().take(fields.len() - 1).zip(fields.iter().skip(1)) {
               match current_struct_info.get(field) {
                  Some(ExpressionType::Value(ValueType::Struct(x))) => {
                     current_struct = *x;
                     current_struct_info = &validation_context.struct_info.get(&current_struct).unwrap().field_types;
                  }
                  Some(_) => {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "Field `{}` is not a struct type and so doesn't have field `{}`",
                        interner.lookup(*field),
                        interner.lookup(*next_field),
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ line {}, column {}",
                        expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
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
                        interner.lookup(current_struct),
                        interner.lookup(*field),
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ line {}, column {}",
                        expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
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
                        interner.lookup(current_struct),
                        interner.lookup(*fields.last().unwrap()),
                     )
                     .unwrap();
                     writeln!(
                        err_stream,
                        "↳ line {}, column {}",
                        expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
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
               lhs.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
            )
            .unwrap();
            expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
         }
      }
      Expression::ArrayLiteral(elems) => {
         for elem in elems.iter_mut() {
            do_type(err_stream, elem, validation_context, interner);
         }

         let mut any_error = false;

         for i in 1..elems.len() {
            try_set_inferred_type(
               &elems[i - 1].exp_type.clone().unwrap(),
               &mut elems[i],
               validation_context,
               err_stream,
               interner,
            );

            if !elems[i - 1].exp_type.as_ref().unwrap().is_concrete_type()
               || !elems[i].exp_type.as_ref().unwrap().is_concrete_type()
            {
               // avoid cascading errors
               continue;
            } else if elems[i - 1].exp_type != elems[i].exp_type {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Element at array index {} has type of {}, but element at array index {} has mismatching type of {}",
                  i - 1,
                  elems[i - 1].exp_type.as_ref().unwrap().as_roland_type_info(interner),
                  i,
                  elems[i].exp_type.as_ref().unwrap().as_roland_type_info(interner),
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ array literal @ line {}, column {}",
                  expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ element {} @ line {}, column {}",
                  i - 1,
                  elems[i - 1].expression_begin_location.line,
                  elems[i - 1].expression_begin_location.col
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ element {} @ line {}, column {}",
                  i, elems[i].expression_begin_location.line, elems[i].expression_begin_location.col
               )
               .unwrap();

               any_error = true;
            }
         }

         if elems.len() > std::u32::MAX as usize {
            any_error = true;
            writeln!(
               err_stream,
               "Array literal has {} elements, which is more than the maximum {} elements",
               elems.len(),
               std::u32::MAX,
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ array literal @ line {}, column {}",
               expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
            )
            .unwrap();
         }

         if any_error {
            expr_node.exp_type = Some(ExpressionType::Value(ValueType::CompileError));
         } else if elems.is_empty() {
            expr_node.exp_type = Some(ExpressionType::Value(ValueType::Array(
               Box::new(ExpressionType::Value(ValueType::Unit)),
               elems.len() as i64,
            )));
         } else {
            let a_type = elems[0].exp_type.clone().unwrap();

            expr_node.exp_type = Some(ExpressionType::Value(ValueType::Array(
               Box::new(a_type),
               elems.len() as i64,
            )));
         }
      }
      Expression::ArrayIndex(array_expression, index_expression) => {
         do_type(err_stream, array_expression, validation_context, interner);
         do_type(err_stream, index_expression, validation_context, interner);

         try_set_inferred_type(
            &ExpressionType::Value(U32_TYPE),
            &mut *index_expression,
            validation_context,
            err_stream,
            interner,
         );

         if !index_expression.exp_type.as_ref().unwrap().is_concrete_type() {
            // avoid cascading errors
         } else if index_expression.exp_type.as_ref().unwrap() != &ExpressionType::Value(U32_TYPE) {
            writeln!(
               err_stream,
               "Attempted to index an array with a value of type {}, which is not u32",
               index_expression
                  .exp_type
                  .as_ref()
                  .unwrap()
                  .as_roland_type_info(interner),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ index @ line {}, column {}",
               index_expression.expression_begin_location.line, index_expression.expression_begin_location.col
            )
            .unwrap();
         }

         expr_node.exp_type = match &array_expression.exp_type {
            Some(ExpressionType::Value(ValueType::CompileError)) => {
               Some(ExpressionType::Value(ValueType::CompileError))
            }
            Some(ExpressionType::Value(ValueType::Array(b, _))) => Some(*b.clone()),
            Some(x) => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Attempted to index expression of type {}, which is not an array type",
                  x.as_roland_type_info(interner),
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ expression @ line {}, column {}",
                  array_expression.expression_begin_location.line, array_expression.expression_begin_location.col
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ index @ line {}, column {}",
                  index_expression.expression_begin_location.line, index_expression.expression_begin_location.col
               )
               .unwrap();

               Some(ExpressionType::Value(ValueType::CompileError))
            }
            None => unreachable!(),
         };
      }
   }
}
