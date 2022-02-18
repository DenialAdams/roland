use super::type_inference::try_set_inferred_type;
use super::{ProcedureInfo, StaticInfo, StructInfo, ValidationContext};
use crate::constant_folding::{try_fold_and_replace_expr, FoldingContext};
use crate::interner::{Interner, StrId};
use crate::lex::{SourceInfo, emit_source_info_with_description, emit_source_info};
use crate::parse::{
   BinOp, BlockNode, Expression, ExpressionId, ExpressionNode, ExpressionPool, IdentifierNode, Program, Statement,
   StatementNode, UnOp,
};
use crate::semantic_analysis::EnumInfo;
use crate::type_data::{ExpressionType, IntType, IntWidth, ValueType, F32_TYPE, F64_TYPE, USIZE_TYPE};
use crate::Target;
use arrayvec::ArrayVec;
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::ops::BitOrAssign;

fn is_special_procedure(target: Target, name: StrId, interner: &mut Interner) -> bool {
   get_special_procedures(target, interner).contains(&name)
}

fn get_special_procedures(target: Target, interner: &mut Interner) -> ArrayVec<StrId, 2> {
   match target {
      Target::Wasm4 => ArrayVec::from([interner.intern("start"), interner.intern("update")]),
      Target::Wasi => [interner.intern("main")].as_slice().try_into().unwrap(),
   }
}

#[derive(Debug)]
enum TypeValidator {
   AnyEnum,
   Bool,
   AnyInt,
   AnySignedInt,
   AnyFloat,
   AnyPointer,
   Any,
}

fn matches(type_validation: &TypeValidator, et: &ExpressionType) -> bool {
   matches!(
      (type_validation, et),
      (TypeValidator::Any, _)
         | (TypeValidator::AnyPointer, ExpressionType::Pointer(_, _))
         | (TypeValidator::Bool, ExpressionType::Value(ValueType::Bool))
         | (TypeValidator::AnyInt, ExpressionType::Value(ValueType::Int(_)))
         | (TypeValidator::AnyInt, ExpressionType::Value(ValueType::UnknownInt))
         | (
            TypeValidator::AnySignedInt,
            ExpressionType::Value(ValueType::Int(IntType { signed: true, .. }))
         )
         | (
            TypeValidator::AnySignedInt,
            // It looks weird that we accept this,
            // but the trick is that we double validate this for the pertinent nodes after we've inferred types
            ExpressionType::Value(ValueType::UnknownInt)
         )
         | (TypeValidator::AnyFloat, ExpressionType::Value(ValueType::Float(_)))
         | (TypeValidator::AnyFloat, ExpressionType::Value(ValueType::UnknownFloat))
         | (TypeValidator::AnyEnum, ExpressionType::Value(ValueType::Enum(_)))
   )
}

fn any_match(type_validations: &[TypeValidator], et: &ExpressionType) -> bool {
   let mut any_match = false;
   for type_validation in type_validations.iter() {
      any_match |= matches(type_validation, et);
   }
   any_match
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum RecursiveStructCheckResult {
   NotRecursive,
   // The struct doesn't contain itself directly or indirectly, but it contains a struct that does
   ContainsRecursiveStruct,
   ContainsSelf,
}

impl BitOrAssign for RecursiveStructCheckResult {
   fn bitor_assign(&mut self, rhs: Self) {
      *self = match (&self, rhs) {
         (RecursiveStructCheckResult::ContainsSelf, _) => RecursiveStructCheckResult::ContainsSelf,
         (RecursiveStructCheckResult::ContainsRecursiveStruct, RecursiveStructCheckResult::ContainsSelf) => {
            RecursiveStructCheckResult::ContainsSelf
         }
         (RecursiveStructCheckResult::ContainsRecursiveStruct, _) => {
            RecursiveStructCheckResult::ContainsRecursiveStruct
         }
         (RecursiveStructCheckResult::NotRecursive, _) => rhs,
      };
   }
}

fn recursive_struct_check(
   base_name: StrId,
   seen_structs: &mut HashSet<StrId>,
   struct_fields: &IndexMap<StrId, ExpressionType>,
   struct_info: &IndexMap<StrId, StructInfo>,
) -> RecursiveStructCheckResult {
   let mut is_recursive = RecursiveStructCheckResult::NotRecursive;

   for struct_field in struct_fields.iter().flat_map(|x| match &x.1 {
      ExpressionType::Value(ValueType::Struct(x)) => Some(*x),
      // Types should be fully resolved at this point, but may not be if there is an error in the program
      // (in that case, it's fine to ignore it as we'll already error out)
      ExpressionType::Value(ValueType::Unresolved(x)) => Some(*x),
      _ => None,
   }) {
      if struct_field == base_name {
         is_recursive = RecursiveStructCheckResult::ContainsSelf;
         break;
      }

      if seen_structs.contains(&struct_field) {
         is_recursive = RecursiveStructCheckResult::ContainsRecursiveStruct;
         continue;
      }

      seen_structs.insert(struct_field);

      is_recursive |= struct_info
         .get(&struct_field)
         .map(|si| recursive_struct_check(base_name, seen_structs, &si.field_types, struct_info))
         .unwrap_or(RecursiveStructCheckResult::NotRecursive);
   }

   is_recursive
}

fn resolve_type(
   t_type: &mut ExpressionType,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) -> Result<(), ()> {
   match t_type {
      ExpressionType::Value(vt) => resolve_value_type(vt, ei, si),
      ExpressionType::Pointer(_, vt) => resolve_value_type(vt, ei, si),
   }
}

fn resolve_value_type(
   v_type: &mut ValueType,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) -> Result<(), ()> {
   match v_type {
      ValueType::UnknownInt => Ok(()),
      ValueType::UnknownFloat => Ok(()),
      ValueType::Int(_) => Ok(()),
      ValueType::Float(_) => Ok(()),
      ValueType::Bool => Ok(()),
      ValueType::Unit => Ok(()),
      ValueType::Struct(_) => Ok(()),
      ValueType::Array(exp, _) => resolve_type(exp, ei, si),
      ValueType::CompileError => Ok(()),
      ValueType::Enum(_) => Ok(()),
      ValueType::Unresolved(x) => {
         if ei.contains_key(x) {
            *v_type = ValueType::Enum(*x);
            Ok(())
         } else if si.contains_key(x) {
            *v_type = ValueType::Struct(*x);
            Ok(())
         } else {
            Err(())
         }
      }
   }
}

pub fn type_and_check_validity<W: Write>(
   program: &mut Program,
   err_stream: &mut W,
   interner: &mut Interner,
   expressions: &mut ExpressionPool,
   target: Target,
) -> u64 {
   let mut procedure_info: IndexMap<StrId, ProcedureInfo> = IndexMap::new();
   let mut enum_info: IndexMap<StrId, EnumInfo> = IndexMap::new();
   let mut struct_info: IndexMap<StrId, StructInfo> = IndexMap::new();
   let mut static_info: IndexMap<StrId, StaticInfo> = IndexMap::new();
   let mut error_count = 0;

   procedure_info.insert(
      interner.intern("sizeof"),
      ProcedureInfo {
         parameters: vec![],
         named_parameters: HashMap::new(),
         type_parameters: 1,
         ret_type: ExpressionType::Value(USIZE_TYPE),
         procedure_begin_location: SourceInfo { line: 0, col: 0, file: None, },
         is_external: true,
      },
   );

   let mut dupe_check = HashSet::new();
   for a_enum in program.enums.iter() {
      dupe_check.clear();
      dupe_check.reserve(a_enum.variants.len());
      for variant in a_enum.variants.iter().copied() {
         if !dupe_check.insert(variant) {
            error_count += 1;
            writeln!(
               err_stream,
               "Enum `{}` has a duplicate variant `{}`",
               interner.lookup(a_enum.name),
               interner.lookup(variant),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ enum defined @ line {}, column {}",
               a_enum.begin_location.line, a_enum.begin_location.col
            )
            .unwrap();
         }
      }

      if let Some(old_enum) = enum_info.insert(
         a_enum.name,
         EnumInfo {
            variants: a_enum.variants.iter().copied().collect(),
            enum_begin_location: a_enum.begin_location,
         },
      ) {
         error_count += 1;
         writeln!(
            err_stream,
            "Encountered duplicate enums with the same name `{}`",
            interner.lookup(a_enum.name)
         )
         .unwrap();
         emit_source_info_with_description(err_stream, old_enum.enum_begin_location, "first enum defined", interner);
         emit_source_info_with_description(err_stream, a_enum.begin_location, "second enum defined", interner);
      }
   }

   for a_struct in program.structs.iter() {
      let mut field_map = IndexMap::with_capacity(a_struct.fields.len());
      for field in a_struct.fields.iter() {
         if field_map.insert(field.0, field.1.clone()).is_some() {
            error_count += 1;
            writeln!(
               err_stream,
               "Struct `{}` has a duplicate field `{}`",
               interner.lookup(a_struct.name),
               interner.lookup(field.0),
            )
            .unwrap();
            emit_source_info_with_description(err_stream, a_struct.begin_location, "struct defined", interner);
         }
      }

      if let Some(old_struct) = struct_info.insert(
         a_struct.name,
         StructInfo {
            field_types: field_map,
            struct_begin_location: a_struct.begin_location,
         },
      ) {
         error_count += 1;
         writeln!(
            err_stream,
            "Encountered duplicate structs with the same name `{}`",
            interner.lookup(a_struct.name)
         )
         .unwrap();
         emit_source_info_with_description(err_stream, old_struct.struct_begin_location, "first struct defined", interner);
         emit_source_info_with_description(err_stream, a_struct.begin_location, "second struct defined", interner);
      }
   }

   // This clone is only necessary for rust's borrowing rules;
   // if hot we can try a different approach
   let cloned_struct_info = struct_info.clone();
   for struct_i in struct_info.iter_mut() {
      if let Some(enum_i) = enum_info.get(struct_i.0) {
         error_count += 1;
         writeln!(
            err_stream,
            "Enum and struct share the same name `{}`",
            interner.lookup(*struct_i.0)
         )
         .unwrap();
         emit_source_info_with_description(err_stream, enum_i.enum_begin_location, "enum defined", interner);
         emit_source_info_with_description(err_stream, struct_i.1.struct_begin_location, "struct defined", interner);
      }

      for (field, e_type) in struct_i.1.field_types.iter_mut() {
         if resolve_type(e_type, &enum_info, &cloned_struct_info).is_ok() {
            continue;
         }

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
         emit_source_info_with_description(err_stream, struct_i.1.struct_begin_location, "struct defined", interner);
      }
   }

   // Check for recursive structs only after we've attempted to resolve all of the field types
   let mut seen_structs = HashSet::new();
   for struct_i in struct_info.iter() {
      seen_structs.clear();
      if recursive_struct_check(*struct_i.0, &mut seen_structs, &struct_i.1.field_types, &struct_info)
         == RecursiveStructCheckResult::ContainsSelf
      {
         error_count += 1;
         writeln!(
            err_stream,
            "Struct `{}` contains itself, which isn't allowed as it would result in an infinitely large struct",
            interner.lookup(*struct_i.0),
         )
         .unwrap();
         emit_source_info_with_description(err_stream, struct_i.1.struct_begin_location, "struct defined", interner);
      }
   }

   for const_node in program.consts.iter_mut() {
      let const_type = &mut const_node.const_type;
      let si = &const_node.begin_location;

      if resolve_type(const_type, &enum_info, &struct_info).is_err() {
         error_count += 1;
         let static_type_str = const_type.as_roland_type_info(interner);
         writeln!(
            err_stream,
            "Const `{}` is of undeclared type `{}`",
            interner.lookup(const_node.name.identifier),
            static_type_str,
         )
         .unwrap();
         emit_source_info_with_description(err_stream, *si, "const defined", interner);
      }

      if let Some(old_value) = static_info.insert(
         const_node.name.identifier,
         StaticInfo {
            static_type: const_node.const_type.clone(),
            begin_location: const_node.begin_location,
            is_const: true,
         },
      ) {
         error_count += 1;
         writeln!(
            err_stream,
            "Encountered duplicate static/const with the same name `{}`",
            interner.lookup(const_node.name.identifier),
         )
         .unwrap();
         emit_source_info_with_description(err_stream, old_value.begin_location, "first static/const defined", interner);
         emit_source_info_with_description(err_stream, const_node.begin_location, "second static/const defined", interner);
      }
   }

   for static_node in program.statics.iter_mut() {
      let static_type = &mut static_node.static_type;
      let si = &static_node.static_begin_location;

      if resolve_type(static_type, &enum_info, &struct_info).is_err() {
         error_count += 1;
         let static_type_str = static_type.as_roland_type_info(interner);
         writeln!(
            err_stream,
            "Static `{}` is of undeclared type `{}`",
            interner.lookup(static_node.name.identifier),
            static_type_str,
         )
         .unwrap();
         emit_source_info_with_description(err_stream, *si, "static defined", interner);
      }

      if let Some(old_value) = static_info.insert(
         static_node.name.identifier,
         StaticInfo {
            static_type: static_node.static_type.clone(),
            begin_location: static_node.static_begin_location,
            is_const: false,
         },
      ) {
         error_count += 1;
         writeln!(
            err_stream,
            "Encountered duplicate static/const with the same name `{}`",
            interner.lookup(static_node.name.identifier),
         )
         .unwrap();
         emit_source_info_with_description(err_stream, old_value.begin_location, "first static/const defined", interner);
         emit_source_info_with_description(err_stream, static_node.static_begin_location, "second static/const defined", interner);
      }
   }

   for (definition, source_location, is_external) in program
      .external_procedures
      .iter_mut()
      .map(|x| (&mut x.definition, x.procedure_begin_location, true))
      .chain(
         program
            .procedures
            .iter_mut()
            .map(|x| (&mut x.definition, x.procedure_begin_location, false)),
      )
   {
      dupe_check.clear();
      dupe_check.reserve(definition.parameters.len());

      let mut first_named_param = None;
      let mut reported_named_error = false;
      for (i, param) in definition.parameters.iter().enumerate() {
         if !dupe_check.insert(param.name) {
            error_count += 1;
            writeln!(
               err_stream,
               "Procedure `{}` has a duplicate parameter `{}`",
               interner.lookup(definition.name),
               interner.lookup(param.name),
            )
            .unwrap();
            emit_source_info_with_description(err_stream, source_location, "procedure declared", interner);
         }

         if param.named && first_named_param.is_none() {
            first_named_param = Some(i);

            if is_external {
               reported_named_error = true;
               error_count += 1;
               writeln!(
                  err_stream,
                  "External procedure `{}` has named parameters, which isn't supported",
                  interner.lookup(definition.name),
               )
               .unwrap();
               emit_source_info_with_description(err_stream, source_location, "procedure declared", interner);
            }
         }

         if !param.named && first_named_param.is_some() && !reported_named_error {
            reported_named_error = true;
            error_count += 1;
            writeln!(
               err_stream,
               "Procedure `{}` has named parameter(s) which come before non-named parameter(s)",
               interner.lookup(definition.name),
            )
            .unwrap();
            emit_source_info_with_description(err_stream, source_location, "procedure declared", interner);
         }
      }

      if !reported_named_error && first_named_param.is_some() {
         if let Some(i) = first_named_param {
            // It doesn't really matter how we sort these, as long as we do it consistently for arguments
            // AND that there are no equal elements (in this case, we already check that parameters don't have the same name)
            definition.parameters[i..].sort_unstable_by_key(|x| x.name);
         }
      }

      for parameter in definition.parameters.iter_mut() {
         if resolve_type(&mut parameter.p_type, &enum_info, &struct_info).is_err() {
            error_count += 1;
            let etype_str = parameter.p_type.as_roland_type_info(interner);
            writeln!(
               err_stream,
               "Parameter `{}` of procedure `{}` is of undeclared type `{}`",
               interner.lookup(parameter.name),
               interner.lookup(definition.name),
               etype_str,
            )
            .unwrap();
            emit_source_info_with_description(err_stream, source_location, "procedure declared", interner);
         }
      }

      if resolve_type(&mut definition.ret_type, &enum_info, &struct_info).is_err() {
         error_count += 1;
         let etype_str = definition.ret_type.as_roland_type_info(interner);
         writeln!(
            err_stream,
            "Return type of procedure `{}` is of undeclared type `{}`",
            interner.lookup(definition.name),
            etype_str,
         )
         .unwrap();
         emit_source_info_with_description(err_stream, source_location, "procedure declared", interner);
      }

      if let Some(old_procedure) = procedure_info.insert(
         definition.name,
         ProcedureInfo {
            type_parameters: 0,
            parameters: definition.parameters.iter().map(|x| x.p_type.clone()).collect(),
            named_parameters: definition
               .parameters
               .iter()
               .filter(|x| x.named)
               .map(|x| (x.name, x.p_type.clone()))
               .collect(),
            ret_type: definition.ret_type.clone(),
            procedure_begin_location: source_location,
            is_external,
         },
      ) {
         error_count += 1;
         let procedure_name_str = interner.lookup(definition.name);
         writeln!(
            err_stream,
            "Encountered duplicate procedures with the same name `{}`",
            procedure_name_str
         )
         .unwrap();
         emit_source_info_with_description(err_stream, old_procedure.procedure_begin_location, "first procedure declared", interner);
         emit_source_info_with_description(err_stream, source_location, "second procedure declared", interner);
      }
   }

   let mut validation_context = ValidationContext {
      target,
      string_literals: IndexSet::new(),
      variable_types: HashMap::new(),
      error_count,
      procedure_info: &procedure_info,
      enum_info: &enum_info,
      struct_info: &struct_info,
      static_info: &static_info,
      cur_procedure_info: None,
      block_depth: 0,
      loop_depth: 0,
      unknown_ints: IndexSet::new(),
      unknown_floats: IndexSet::new(),
      expressions,
   };

   let special_procs = get_special_procedures(target, interner);
   for special_proc_name in special_procs.iter().copied() {
      if !validation_context.procedure_info.contains_key(&special_proc_name) {
         validation_context.error_count += 1;
         writeln!(
            err_stream,
            "A procedure with the name `{}` must be present for this target ({})",
            interner.lookup(special_proc_name),
            validation_context.target,
         )
         .unwrap();
      } else if validation_context
         .procedure_info
         .get(&special_proc_name)
         .unwrap()
         .ret_type
         != ExpressionType::Value(ValueType::Unit)
         || !validation_context
            .procedure_info
            .get(&special_proc_name)
            .unwrap()
            .parameters
            .is_empty()
      {
         validation_context.error_count += 1;
         writeln!(
            err_stream,
            "`{}` is a special procedure for this target ({}) and is not allowed to return a value or take arguments",
            interner.lookup(special_proc_name),
            validation_context.target,
         ).unwrap();
         let si = validation_context
            .procedure_info
            .get(&special_proc_name)
            .unwrap()
            .procedure_begin_location;
         emit_source_info_with_description(err_stream, si, "defined", interner);
      }
   }

   // We won't proceed with type checking because there could be false positives due to
   // procedure/struct definition errors, and probably invalidated invariants
   if validation_context.error_count > 0 {
      return validation_context.error_count;
   }

   for p_const in program.consts.iter_mut() {
      // p_const.const_type is guaranteed to be resolved at this point
      type_expression(err_stream, p_const.value, &mut validation_context, interner);
      try_set_inferred_type(
         &p_const.const_type,
         p_const.value,
         &mut validation_context,
         err_stream,
         interner,
      );

      // In a seperate scope for borrowck
      {
         let p_const_expr = &validation_context.expressions[p_const.value];

         if p_const.const_type != *p_const_expr.exp_type.as_ref().unwrap()
            && !p_const_expr.exp_type.as_ref().unwrap().is_error_type()
         {
            validation_context.error_count += 1;
            let actual_type_str = p_const_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
            writeln!(
               err_stream,
               "Declared type {} of const `{}` does not match actual expression type {}",
               p_const.const_type.as_roland_type_info(interner),
               interner.lookup(p_const.name.identifier),
               actual_type_str,
            )
            .unwrap();
            emit_source_info_with_description(err_stream, p_const.begin_location, "const", interner);
            emit_source_info_with_description(err_stream, p_const_expr.expression_begin_location, "expression", interner);
         }
      }

      try_fold_and_replace_expr(
         p_const.value,
         err_stream,
         &mut FoldingContext {
            error_count: 0,
            expressions: validation_context.expressions,
         },
         interner,
      );
      let p_const_expr = &validation_context.expressions[p_const.value];

      if !crate::constant_folding::is_const(&p_const_expr.expression, validation_context.expressions) {
         validation_context.error_count += 1;
         writeln!(
            err_stream,
            "Value of const `{}` can't be constant folded. Hint: Either simplify the expression, or turn the constant into a static and initialize it on program start.",
            interner.lookup(p_const.name.identifier),
         )
         .unwrap();
         emit_source_info_with_description(err_stream, p_const.begin_location, "const", interner);
         emit_source_info_with_description(err_stream, p_const_expr.expression_begin_location, "expression", interner);
      }
   }

   for p_static in program.statics.iter_mut().filter(|x| x.value.is_some()) {
      // p_static.static_type is guaranteed to be resolved at this point
      type_expression(err_stream, p_static.value.unwrap(), &mut validation_context, interner);
      try_set_inferred_type(
         &p_static.static_type,
         p_static.value.unwrap(),
         &mut validation_context,
         err_stream,
         interner,
      );

      let p_static_expr = &validation_context.expressions[p_static.value.unwrap()];

      if p_static.static_type != *p_static_expr.exp_type.as_ref().unwrap()
         && !p_static_expr.exp_type.as_ref().unwrap().is_error_type()
      {
         validation_context.error_count += 1;
         let actual_type_str = p_static_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
         writeln!(
            err_stream,
            "Declared type {} of static `{}` does not match actual expression type {}",
            p_static.static_type.as_roland_type_info(interner),
            interner.lookup(p_static.name.identifier),
            actual_type_str,
         )
         .unwrap();
         emit_source_info_with_description(err_stream, p_static.static_begin_location, "static", interner);
         emit_source_info_with_description(err_stream, p_static_expr.expression_begin_location, "expression", interner);
      }

      if let Some(v) = p_static.value.as_mut() {
         try_fold_and_replace_expr(
            *v,
            err_stream,
            &mut FoldingContext {
               error_count: 0,
               expressions: validation_context.expressions,
            },
            interner
         );
         let v = &validation_context.expressions[*v];
         if !crate::constant_folding::is_const(&v.expression, validation_context.expressions) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Value of static `{}` can't be constant folded. Hint: Either simplify the expression, or initialize it yourself on program start.",
               interner.lookup(p_static.name.identifier),
            )
            .unwrap();
            emit_source_info_with_description(err_stream, p_static.static_begin_location, "static", interner);
            emit_source_info_with_description(err_stream, v.expression_begin_location, "expression", interner);
         }
      }
   }

   for procedure in program.procedures.iter_mut() {
      validation_context.variable_types.clear();
      validation_context.cur_procedure_info = procedure_info.get(&procedure.definition.name);

      for parameter in procedure.definition.parameters.iter() {
         validation_context
            .variable_types
            .insert(parameter.name, (parameter.p_type.clone(), 0));
         procedure
            .locals
            .entry(parameter.name)
            .or_insert_with(HashSet::new)
            .insert(parameter.p_type.clone());
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
         &procedure.definition.ret_type,
         procedure.block.statements.last().map(|x| &x.statement),
      ) {
         (ExpressionType::Value(ValueType::Unit), _) => (),
         (_, Some(Statement::Return(_))) => (),
         (x, _) => {
            validation_context.error_count += 1;
            let x_str = x.as_roland_type_info(interner);
            writeln!(
               err_stream,
               "Procedure `{}` is declared to return type {} but is missing a final return statement",
               interner.lookup(procedure.definition.name),
               x_str,
            )
            .unwrap();
            emit_source_info_with_description(err_stream, procedure.procedure_begin_location, "procedure defined", interner);
            if let Some(fs) = procedure.block.statements.last() {
               emit_source_info_with_description(err_stream, fs.statement_begin_location, "actual final statement", interner);
            }
         }
      }
   }

   if !validation_context.unknown_ints.is_empty() {
      validation_context.error_count += 1;
      writeln!(
         err_stream,
         "We weren't able to determine the types of {} int literals",
         validation_context.unknown_ints.len()
      )
      .unwrap();
      for expr_id in validation_context.unknown_ints.iter() {
         let loc = validation_context.expressions[*expr_id].expression_begin_location;
         emit_source_info(err_stream, loc, interner);
      }
   }

   if !validation_context.unknown_floats.is_empty() {
      validation_context.error_count += 1;
      writeln!(
         err_stream,
         "We weren't able to determine the types of {} float literals",
         validation_context.unknown_floats.len()
      )
      .unwrap();
      for expr_id in validation_context.unknown_ints.iter() {
         let loc = validation_context.expressions[*expr_id].expression_begin_location;
         emit_source_info(err_stream, loc, interner);
      }
   }

   let err_count = validation_context.error_count;
   program.literals = validation_context.string_literals;
   program.enum_info = enum_info;
   program.struct_info = struct_info;
   program.static_info = static_info;

   err_count
}

fn type_statement<W: Write>(
   err_stream: &mut W,
   statement: &mut StatementNode,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut IndexMap<StrId, HashSet<ExpressionType>>,
   interner: &mut Interner,
) {
   match &mut statement.statement {
      Statement::Assignment(lhs, rhs) => {
         type_expression(err_stream, *lhs, validation_context, interner);
         type_expression(err_stream, *rhs, validation_context, interner);

         try_set_inferred_type(
            &validation_context.expressions[*lhs].exp_type.clone().unwrap(),
            *rhs,
            validation_context,
            err_stream,
            interner,
         );

         let len = &validation_context.expressions[*lhs];
         let en = &validation_context.expressions[*rhs];

         let lhs_type = len.exp_type.as_ref().unwrap();
         let rhs_type = en.exp_type.as_ref().unwrap();

         if lhs_type.is_error_type()
            || rhs_type.is_error_type()
         {
            // avoid cascading errors
         } else if lhs_type != rhs_type {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Left hand side of assignment has type {} which does not match the type of the right hand side {}",
               lhs_type.as_roland_type_info(interner),
               rhs_type.as_roland_type_info(interner),
            )
            .unwrap();
            emit_source_info_with_description(err_stream, len.expression_begin_location, "left hand side", interner);
            emit_source_info_with_description(err_stream, en.expression_begin_location, "right hand side", interner);
         } else if !len
            .expression
            .is_lvalue(validation_context.expressions, validation_context.static_info)
         {
            validation_context.error_count += 1;
            if len
               .expression
               .is_lvalue_disregard_consts(validation_context.expressions)
            {
               writeln!(
                  err_stream,
                  "Left hand side of assignment is a constant, which does not have a memory location and can't be reassigned"
               )
               .unwrap();
               emit_source_info(err_stream, len.expression_begin_location, interner);
            } else {
               writeln!(
                  err_stream,
                  "Left hand side of assignment is not a valid memory location; i.e. a variable, field, or array index"
               )
               .unwrap();
               emit_source_info(err_stream, len.expression_begin_location, interner);
            }
         }
      }
      Statement::Block(bn) => {
         type_block(err_stream, bn, validation_context, cur_procedure_locals, interner);
      }
      Statement::Continue => {
         if validation_context.loop_depth == 0 {
            validation_context.error_count += 1;
            writeln!(err_stream, "Continue statement can only be used in a loop").unwrap();
            emit_source_info(err_stream, statement.statement_begin_location, interner);
         }
      }
      Statement::Break => {
         if validation_context.loop_depth == 0 {
            validation_context.error_count += 1;
            writeln!(err_stream, "Break statement can only be used in a loop").unwrap();
            emit_source_info(err_stream, statement.statement_begin_location, interner);
         }
      }
      Statement::For(var, start, end, bn, _) => {
         type_expression(err_stream, *start, validation_context, interner);
         type_expression(err_stream, *end, validation_context, interner);

         try_set_inferred_type(
            &validation_context.expressions[*start].exp_type.clone().unwrap(),
            *end,
            validation_context,
            err_stream,
            interner,
         );
         try_set_inferred_type(
            &validation_context.expressions[*end].exp_type.clone().unwrap(),
            *start,
            validation_context,
            err_stream,
            interner,
         );

         let start_expr = &validation_context.expressions[*start];
         let end_expr = &validation_context.expressions[*end];

         let result_type = match (
            start_expr.exp_type.as_ref().unwrap(),
            end_expr.exp_type.as_ref().unwrap(),
         ) {
            (lhs, _) if lhs.is_error_type() => ExpressionType::Value(ValueType::CompileError),
            (_, rhs) if rhs.is_error_type() => ExpressionType::Value(ValueType::CompileError),
            (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) if x == y => {
               ExpressionType::Value(ValueType::Int(*x))
            }
            _ => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Start and end of range must be integer types of the same kind; got types `{}` and `{}`",
                  start_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
                  end_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
               )
               .unwrap();
               emit_source_info_with_description(err_stream, start_expr.expression_begin_location, "start of range", interner);
               emit_source_info_with_description(err_stream, end_expr.expression_begin_location, "end of range", interner);
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         // This way the variable is declared at the depth that we'll be typing in
         validation_context.block_depth += 1;
         declare_variable(
            err_stream,
            var,
            result_type,
            validation_context,
            cur_procedure_locals,
            interner,
         );
         validation_context.block_depth -= 1;

         validation_context.loop_depth += 1;
         type_block(err_stream, bn, validation_context, cur_procedure_locals, interner);
         validation_context.loop_depth -= 1;
      }
      Statement::Loop(bn) => {
         validation_context.loop_depth += 1;
         type_block(err_stream, bn, validation_context, cur_procedure_locals, interner);
         validation_context.loop_depth -= 1;
      }
      Statement::Expression(en) => {
         type_expression(err_stream, *en, validation_context, interner);
      }
      Statement::IfElse(en, block_1, block_2) => {
         type_block(err_stream, block_1, validation_context, cur_procedure_locals, interner);
         type_statement(err_stream, block_2, validation_context, cur_procedure_locals, interner);
         type_expression(err_stream, *en, validation_context, interner);

         let en = &validation_context.expressions[*en];
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if if_exp_type != &ExpressionType::Value(ValueType::Bool)
            && !if_exp_type.is_error_type()
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Value of if expression must be a bool; got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            )
            .unwrap();
            emit_source_info(err_stream, en.expression_begin_location, interner);
         }
      }
      Statement::Return(en) => {
         type_expression(err_stream, *en, validation_context, interner);
         let cur_procedure_info = validation_context.cur_procedure_info.unwrap();

         // Type Inference
         try_set_inferred_type(
            &cur_procedure_info.ret_type,
            *en,
            validation_context,
            err_stream,
            interner,
         );

         let en = &validation_context.expressions[*en];

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
            emit_source_info(err_stream, en.expression_begin_location, interner);
         }
      }
      Statement::VariableDeclaration(id, en, dt) => {
         type_expression(err_stream, *en, validation_context, interner);

         if let Some(v) = dt.as_mut() {
            // Failure to resolve is handled below
            let _ = resolve_type(v, validation_context.enum_info, validation_context.struct_info);
            try_set_inferred_type(v, *en, validation_context, err_stream, interner);
         }

         let en = &validation_context.expressions[*en];

         let result_type = if dt.is_some()
            && *dt != en.exp_type
            && !en.exp_type.as_ref().unwrap().is_error_type()
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Declared type {} does not match actual expression type {}",
               dt.as_ref().unwrap().as_roland_type_info(interner),
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            )
            .unwrap();
            emit_source_info_with_description(err_stream, statement.statement_begin_location, "declaration", interner);
            emit_source_info_with_description(err_stream, en.expression_begin_location, "expression", interner);
            ExpressionType::Value(ValueType::CompileError)
         } else if dt
            .as_ref()
            .map(|x| matches!(x, ExpressionType::Value(ValueType::Unresolved(_))))
            .unwrap_or(false)
         {
            validation_context.error_count += 1;
            let dt_str = dt.as_ref().unwrap().as_roland_type_info(interner);
            writeln!(
               err_stream,
               "Variable `{}` is declared with undefined type `{}`",
               interner.lookup(id.identifier),
               dt_str,
            )
            .unwrap();
            emit_source_info_with_description(err_stream, statement.statement_begin_location, "declaration", interner);
            ExpressionType::Value(ValueType::CompileError)
         } else {
            en.exp_type.clone().unwrap()
         };

         declare_variable(
            err_stream,
            id,
            result_type,
            validation_context,
            cur_procedure_locals,
            interner,
         );
      }
   }
}

fn declare_variable<W: Write>(
   err_stream: &mut W,
   id: &IdentifierNode,
   var_type: ExpressionType,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut IndexMap<StrId, HashSet<ExpressionType>>,
   interner: &mut Interner,
) {
   if validation_context.static_info.contains_key(&id.identifier)
      || validation_context.variable_types.contains_key(&id.identifier)
   {
      validation_context.error_count += 1;
      writeln!(
         err_stream,
         "Variable shadowing is not supported at this time (`{}`)",
         interner.lookup(id.identifier)
      )
      .unwrap();
      emit_source_info_with_description(err_stream, id.begin_location, "declaration", interner);
   } else {
      validation_context
         .variable_types
         .insert(id.identifier, (var_type.clone(), validation_context.block_depth));
      cur_procedure_locals
         .entry(id.identifier)
         .or_insert_with(HashSet::new)
         .insert(var_type);
   }
}

fn type_block<W: Write>(
   err_stream: &mut W,
   bn: &mut BlockNode,
   validation_context: &mut ValidationContext,
   cur_procedure_locals: &mut IndexMap<StrId, HashSet<ExpressionType>>,
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

fn get_type<W: Write>(
   err_stream: &mut W,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) -> ExpressionType {
   let expr_location = validation_context.expressions[expr_index].expression_begin_location;

   // SAFETY: it's paramount that this pointer stays valid, so we can't let the expression array resize
   // while this pointer is alive. We don't do this, because we update this expression in place and don't
   // add new expressions during validation.
   let expr_node = &mut validation_context.expressions[expr_index] as *mut ExpressionNode;

   match unsafe { &mut (*expr_node).expression } {
      Expression::UnitLiteral => ExpressionType::Value(ValueType::Unit),
      Expression::BoolLiteral(_) => ExpressionType::Value(ValueType::Bool),
      Expression::IntLiteral(_) => {
         validation_context.unknown_ints.insert(expr_index);
         ExpressionType::Value(ValueType::UnknownInt)
      }
      Expression::FloatLiteral(_) => {
         validation_context.unknown_floats.insert(expr_index);
         ExpressionType::Value(ValueType::UnknownFloat)
      }
      Expression::StringLiteral(lit) => {
         validation_context.string_literals.insert(*lit);
         ExpressionType::Value(ValueType::Struct(interner.intern("String")))
      }
      Expression::Extend(target_type, e) => {
         type_expression(err_stream, *e, validation_context, interner);

         let e = &validation_context.expressions[*e];
         let e_type = e.exp_type.as_ref().unwrap();

         if resolve_type(
            target_type,
            validation_context.enum_info,
            validation_context.struct_info,
         )
         .is_err()
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Undeclared type `{}`",
               target_type.as_roland_type_info(interner),
            )
            .unwrap();
            emit_source_info(err_stream, expr_location, interner);

            ExpressionType::Value(ValueType::CompileError)
         } else if !e_type.is_concrete_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else {
            let valid_cast = match (e_type, &target_type) {
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                  if x.width == IntWidth::Pointer =>
               {
                  IntWidth::Pointer.as_num_bytes() <= y.width.as_num_bytes()
               }
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                  if y.width == IntWidth::Pointer =>
               {
                  x.width.as_num_bytes() <= IntWidth::Pointer.as_num_bytes()
               }
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                  x.width.as_num_bytes() < y.width.as_num_bytes()
               }
               (ExpressionType::Value(F32_TYPE), ExpressionType::Value(F64_TYPE)) => true,
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
               emit_source_info_with_description(err_stream, expr_location, "extend", interner);
               emit_source_info_with_description(err_stream, e.expression_begin_location, "operand", interner);
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::Transmute(target_type, e) => {
         type_expression(err_stream, *e, validation_context, interner);

         if target_type.is_pointer() {
            try_set_inferred_type(
               &ExpressionType::Value(USIZE_TYPE),
               *e,
               validation_context,
               err_stream,
               interner,
            );
         }

         let e = &validation_context.expressions[*e];
         let e_type = e.exp_type.as_ref().unwrap();

         if resolve_type(
            target_type,
            validation_context.enum_info,
            validation_context.struct_info,
         )
         .is_err()
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Undeclared type `{}`",
               target_type.as_roland_type_info(interner),
            )
            .unwrap();
            emit_source_info(err_stream, expr_location, interner);

            ExpressionType::Value(ValueType::CompileError)
         } else if !e_type.is_concrete_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else {
            let valid_cast = match (e_type, &target_type) {
               (ExpressionType::Pointer(_, _), ExpressionType::Pointer(_, _)) => true,
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Pointer(_, _))
                  if x.width == IntWidth::Pointer =>
               {
                  true
               }
               (ExpressionType::Pointer(_, _), ExpressionType::Value(ValueType::Int(x)))
                  if x.width == IntWidth::Pointer =>
               {
                  true
               }
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                  x.width.as_num_bytes() == y.width.as_num_bytes()
               }
               (ExpressionType::Value(ValueType::Float(x)), ExpressionType::Value(ValueType::Int(y))) => {
                  x.width.as_num_bytes() == y.width.as_num_bytes()
               }
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Float(y))) => {
                  x.width.as_num_bytes() == y.width.as_num_bytes()
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
               emit_source_info_with_description(err_stream, expr_location, "transmute", interner);
               emit_source_info_with_description(err_stream, e.expression_begin_location, "operand", interner);
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::Truncate(target_type, e) => {
         type_expression(err_stream, *e, validation_context, interner);

         let e = &validation_context.expressions[*e];
         let e_type = e.exp_type.as_ref().unwrap();

         if resolve_type(
            target_type,
            validation_context.enum_info,
            validation_context.struct_info,
         )
         .is_err()
         {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Undeclared type `{}`",
               target_type.as_roland_type_info(interner),
            )
            .unwrap();
            emit_source_info(err_stream, expr_location, interner);

            ExpressionType::Value(ValueType::CompileError)
         } else if !e_type.is_concrete_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else {
            let valid_cast = match (e_type, &target_type) {
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                  if x.width == IntWidth::Pointer =>
               {
                  IntWidth::Pointer.as_num_bytes() >= y.width.as_num_bytes()
               }
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                  if y.width == IntWidth::Pointer =>
               {
                  x.width.as_num_bytes() >= IntWidth::Pointer.as_num_bytes()
               }
               (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                  x.width.as_num_bytes() > y.width.as_num_bytes()
               }
               (ExpressionType::Value(F64_TYPE), ExpressionType::Value(F32_TYPE)) => true,
               (ExpressionType::Value(ValueType::Float(_)), ExpressionType::Value(ValueType::Int(_))) => true,
               (ExpressionType::Value(ValueType::Int(_)), ExpressionType::Value(ValueType::Float(_))) => true,
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
               emit_source_info_with_description(err_stream, expr_location, "truncate", interner);
               emit_source_info_with_description(err_stream, e.expression_begin_location, "operand", interner);
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::BinaryOperator { operator, lhs, rhs } => {
         type_expression(err_stream, *lhs, validation_context, interner);
         type_expression(err_stream, *rhs, validation_context, interner);

         let correct_arg_types: &[TypeValidator] = match operator {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::GreaterThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThan
            | BinOp::LessThanOrEqualTo => &[TypeValidator::AnyInt, TypeValidator::AnyFloat],
            BinOp::LogicalAnd | BinOp::LogicalOr => &[TypeValidator::Bool],
            BinOp::Equality | BinOp::NotEquality => &[
               TypeValidator::AnyInt,
               TypeValidator::Bool,
               TypeValidator::AnyEnum,
               TypeValidator::AnyFloat,
            ],
            BinOp::BitwiseAnd | BinOp::BitwiseOr | BinOp::BitwiseXor => &[TypeValidator::AnyInt, TypeValidator::Bool],
            BinOp::BitwiseLeftShift | BinOp::BitwiseRightShift | BinOp::Remainder => &[TypeValidator::AnyInt],
         };

         try_set_inferred_type(
            &validation_context.expressions[*lhs].exp_type.clone().unwrap(),
            *rhs,
            validation_context,
            err_stream,
            interner,
         );
         try_set_inferred_type(
            &validation_context.expressions[*rhs].exp_type.clone().unwrap(),
            *lhs,
            validation_context,
            err_stream,
            interner,
         );

         let lhs_expr = &validation_context.expressions[*lhs];
         let rhs_expr = &validation_context.expressions[*rhs];

         let lhs_type = lhs_expr.exp_type.as_ref().unwrap();
         let rhs_type = rhs_expr.exp_type.as_ref().unwrap();

         if lhs_type.is_error_type()
            || rhs_type.is_error_type()
         {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_arg_types, lhs_type) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {}",
               operator,
               correct_arg_types,
               lhs_type.as_roland_type_info(interner)
            )
            .unwrap();
            emit_source_info(err_stream, lhs_expr.expression_begin_location, interner);
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_arg_types, rhs_type) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Binary operator {:?} requires RHS to have type matching {:?}; instead got {}",
               operator,
               correct_arg_types,
               rhs_type.as_roland_type_info(interner)
            )
            .unwrap();
            emit_source_info(err_stream, rhs_expr.expression_begin_location, interner);
            ExpressionType::Value(ValueType::CompileError)
         } else if lhs_type != rhs_type {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Binary operator {:?} requires LHS and RHS to have identical type; instead got {} and {}",
               operator,
               lhs_type.as_roland_type_info(interner),
               rhs_type.as_roland_type_info(interner)
            )
            .unwrap();
            emit_source_info_with_description(err_stream, lhs_expr.expression_begin_location, "lef hand side", interner);
            emit_source_info_with_description(err_stream, rhs_expr.expression_begin_location, "right hand side", interner);
            ExpressionType::Value(ValueType::CompileError)
         } else {
            match operator {
               BinOp::Add
               | BinOp::Subtract
               | BinOp::Multiply
               | BinOp::Divide
               | BinOp::Remainder
               | BinOp::BitwiseAnd
               | BinOp::BitwiseOr
               | BinOp::BitwiseXor
               | BinOp::BitwiseLeftShift
               | BinOp::BitwiseRightShift => lhs_type.clone(),
               BinOp::Equality
               | BinOp::NotEquality
               | BinOp::GreaterThan
               | BinOp::GreaterThanOrEqualTo
               | BinOp::LessThan
               | BinOp::LessThanOrEqualTo
               | BinOp::LogicalAnd
               | BinOp::LogicalOr => ExpressionType::Value(ValueType::Bool),
            }
         }
      }
      Expression::UnaryOperator(un_op, e) => {
         type_expression(err_stream, *e, validation_context, interner);

         let e = &validation_context.expressions[*e];

         let (correct_type, node_type): (&[TypeValidator], _) = match un_op {
            UnOp::Dereference => {
               let mut new_type = e.exp_type.clone().unwrap();
               // If this fails, it will be caught by the type matcher
               let _ = new_type.decrement_indirection_count();
               (&[TypeValidator::AnyPointer], new_type)
            }
            UnOp::Negate => (
               &[TypeValidator::AnySignedInt, TypeValidator::AnyFloat],
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

         if e.exp_type.as_ref().unwrap().is_error_type() {
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
            emit_source_info(err_stream, e.expression_begin_location, interner);
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::AddressOf
            && !e
               .expression
               .is_lvalue(validation_context.expressions, validation_context.static_info)
         {
            validation_context.error_count += 1;
            if e.expression.is_lvalue_disregard_consts(validation_context.expressions) {
               writeln!(
                  err_stream,
                  "Attempting to take a pointer to a const, which can't be done as they don't reside in memory"
               )
               .unwrap();
               emit_source_info(err_stream, expr_location, interner);
            } else {
               writeln!(
                  err_stream,
                  "A pointer can only be taken to a value that resides in memory; i.e. a variable or parameter"
               )
               .unwrap();
               emit_source_info(err_stream, expr_location, interner);
            }
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::AddressOf {
            if let Expression::Variable(var) = e.expression {
               if validation_context
                  .static_info
                  .get(&var)
                  .map(|x| x.is_const)
                  .unwrap_or(false)
               {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "Attempting to take a pointer to a const, which does not have a memory location. Hint: Should `{}` be a static?",
                     interner.lookup(var),
                  )
                  .unwrap();
                  emit_source_info(err_stream, expr_location, interner);
               }
            }
            node_type
         } else {
            node_type
         }
      }
      Expression::Variable(id) => {
         let defined_type = validation_context
            .static_info
            .get(id)
            .map(|x| &x.static_type)
            .or_else(|| validation_context.variable_types.get(id).map(|x| &x.0));

         match defined_type {
            Some(t) => t.clone(),
            None => {
               validation_context.error_count += 1;
               writeln!(err_stream, "Encountered undefined variable `{}`", interner.lookup(*id)).unwrap();
               emit_source_info(err_stream, expr_location, interner);
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::ProcedureCall {
         proc_name,
         args,
         generic_args,
      } => {
         for arg in args.iter_mut() {
            type_expression(err_stream, arg.expr, validation_context, interner);
         }

         for g_arg in generic_args.iter_mut() {
            if resolve_type(
               &mut g_arg.gtype,
               validation_context.enum_info,
               validation_context.struct_info,
            )
            .is_err()
            {
               validation_context.error_count += 1;
               let etype_str = g_arg.gtype.as_roland_type_info(interner);
               writeln!(
                  err_stream,
                  "Undeclared type `{}` given as a type argument to `{}`",
                  etype_str,
                  interner.lookup(*proc_name),
               )
               .unwrap();
               emit_source_info_with_description(err_stream, expr_location, "call", interner);
            }
         }

         if is_special_procedure(validation_context.target, *proc_name, interner) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "`{}` is a special procedure and is not allowed to be called",
               interner.lookup(*proc_name),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               expr_location.line, expr_location.col
            )
            .unwrap();
            emit_source_info(err_stream, expr_location, interner);
         }

         match validation_context.procedure_info.get(proc_name) {
            Some(procedure_info) => {
               // Validate that there are no non-named arguments after named arguments, then reorder the argument list
               let first_named_arg = args.iter().enumerate().find(|(_, arg)| arg.name.is_some()).map(|x| x.0);
               let last_normal_arg = args
                  .iter()
                  .enumerate()
                  .rfind(|(_, arg)| arg.name.is_none())
                  .map(|x| x.0);
               let args_in_order = first_named_arg
                  .and_then(|x| last_normal_arg.map(|y| x > y))
                  .unwrap_or(true);

               if !args_in_order {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "Call to `{}` has named argument(s) which come before non-named argument(s)",
                     interner.lookup(*proc_name),
                  )
                  .unwrap();
                  emit_source_info(err_stream, expr_location, interner);
               }

               if procedure_info.type_parameters != generic_args.len() {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "In call to `{}`, mismatched arity. Expected {} type arguments but got {}",
                     interner.lookup(*proc_name),
                     procedure_info.type_parameters,
                     generic_args.len()
                  )
                  .unwrap();
                  emit_source_info(err_stream, expr_location, interner);
               }

               if args_in_order && procedure_info.parameters.len() != args.len() {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "In call to `{}`, mismatched arity. Expected {} arguments but got {}",
                     interner.lookup(*proc_name),
                     procedure_info.parameters.len(),
                     args.len()
                  )
                  .unwrap();
                  emit_source_info(err_stream, expr_location, interner);
                  // We shortcircuit here, because there will likely be lots of mismatched types if an arg was forgotten
               } else if args_in_order {
                  let expected_types = procedure_info.parameters.iter();
                  for (i, (actual, expected)) in args.iter_mut().zip(expected_types).enumerate() {
                     // These should be at the end by now, so we've checked everything we needed to
                     if actual.name.is_some() {
                        break;
                     }

                     try_set_inferred_type(expected, actual.expr, validation_context, err_stream, interner);

                     let actual_expr = &validation_context.expressions[actual.expr];
                     let actual_type = actual_expr.exp_type.as_ref().unwrap();

                     if actual_type != expected && !actual_type.is_error_type() {
                        validation_context.error_count += 1;
                        let actual_type_str = actual_type.as_roland_type_info(interner);
                        let expected_type_str = expected.as_roland_type_info(interner);
                        writeln!(
                           err_stream,
                           "In call to `{}`, encountered argument of type {} when we expected {}",
                           interner.lookup(*proc_name),
                           actual_type_str,
                           expected_type_str,
                        )
                        .unwrap();
                        writeln!(
                           err_stream,
                           "↳ argument at position {}",
                           i
                        )
                        .unwrap();
                        emit_source_info(err_stream, expr_location, interner);
                     }
                  }

                  for arg in args.iter_mut().filter(|x| x.name.is_some()) {
                     let expected = procedure_info.named_parameters.get(&arg.name.unwrap());

                     if expected.is_none() {
                        validation_context.error_count += 1;
                        writeln!(
                           err_stream,
                           "In call to `{}`, encountered named argument `{}` that does not correspond to any named parameter",
                           interner.lookup(*proc_name),
                           interner.lookup(arg.name.unwrap()),
                        )
                        .unwrap();
                        emit_source_info(err_stream, expr_location, interner);
                        continue;
                     }

                     let expected = expected.unwrap();

                     try_set_inferred_type(expected, arg.expr, validation_context, err_stream, interner);

                     let arg_expr = &validation_context.expressions[arg.expr];

                     let actual_type = arg_expr.exp_type.as_ref().unwrap();
                     if actual_type != expected && !actual_type.is_error_type() {
                        validation_context.error_count += 1;
                        let actual_type_str = actual_type.as_roland_type_info(interner);
                        let expected_type_str = expected.as_roland_type_info(interner);
                        writeln!(
                           err_stream,
                           "In call to `{}`, encountered argument of type {} when we expected {} for named parameter {}",
                           interner.lookup(*proc_name),
                           actual_type_str,
                           expected_type_str,
                           interner.lookup(arg.name.unwrap())
                        )
                        .unwrap();
                        emit_source_info(err_stream, expr_location, interner);
                     }
                  }
               }

               procedure_info.ret_type.clone()
            }
            None => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Encountered call to undefined procedure `{}`",
                  interner.lookup(*proc_name),
               )
               .unwrap();
               emit_source_info(err_stream, expr_location, interner);
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::StructLiteral(struct_name, fields) => {
         for field in fields.iter_mut() {
            type_expression(err_stream, field.1, validation_context, interner);
         }

         match validation_context.struct_info.get(struct_name) {
            Some(defined_struct) => {
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
                        emit_source_info_with_description(err_stream, defined_struct.struct_begin_location, "struct defined", interner);
                        emit_source_info_with_description(err_stream, expr_location, "struct instantiated", interner);
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
                     emit_source_info_with_description(err_stream, defined_struct.struct_begin_location, "struct defined", interner);
                     emit_source_info_with_description(err_stream, expr_location, "struct instantiated", interner);
                  }

                  try_set_inferred_type(defined_type, field.1, validation_context, err_stream, interner);

                  let field_expr = &validation_context.expressions[field.1];

                  if field_expr.exp_type.as_ref().unwrap() != defined_type
                     && field_expr.exp_type.as_ref().unwrap().is_concrete_type()
                  {
                     validation_context.error_count += 1;
                     let field_1_type_str = field_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
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
                     emit_source_info_with_description(err_stream, defined_struct.struct_begin_location, "struct defined", interner);
                     emit_source_info_with_description(err_stream, expr_location, "struct instantiated", interner);
                     emit_source_info_with_description(err_stream, field_expr.expression_begin_location, "field_value", interner);
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
                  emit_source_info_with_description(err_stream, defined_struct.struct_begin_location, "struct defined", interner);
                  emit_source_info_with_description(err_stream, expr_location, "struct instantiated", interner);
               }

               ExpressionType::Value(ValueType::Struct(*struct_name))
            }
            None => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Encountered construction of undefined struct `{}`",
                  interner.lookup(*struct_name)
               )
               .unwrap();
               emit_source_info(err_stream, expr_location, interner);
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::FieldAccess(fields, lhs) => {
         type_expression(err_stream, *lhs, validation_context, interner);

         let lhs = &validation_context.expressions[*lhs];
         let mut lhs_type = lhs.exp_type.as_ref().unwrap().clone();
         let mut remaining_fields = fields.as_slice();

         let length_token = interner.intern("length");

         while !remaining_fields.is_empty() {
            let field = remaining_fields[0];
            match lhs_type {
               ExpressionType::Value(ValueType::Struct(struct_name)) => {
                  let struct_fields = &validation_context.struct_info.get(&struct_name).unwrap().field_types;
                  if let Some(new_t) = struct_fields.get(&field) {
                     lhs_type = new_t.clone();
                  } else {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "Struct `{}` does not have a field `{}`",
                        interner.lookup(struct_name),
                        interner.lookup(field),
                     )
                     .unwrap();
                     emit_source_info(err_stream, expr_location, interner);
                     lhs_type = ExpressionType::Value(ValueType::CompileError);
                  }
               }
               ExpressionType::Value(ValueType::Array(_, _)) => {
                  if field != length_token {
                     validation_context.error_count += 1;
                     writeln!(
                        err_stream,
                        "Array does not have a field `{}`. Hint: Array types have a single field `length`",
                        interner.lookup(*fields.first().unwrap()),
                     )
                     .unwrap();
                     emit_source_info(err_stream, expr_location, interner);
                     lhs_type = ExpressionType::Value(ValueType::CompileError);
                  } else {
                     lhs_type = ExpressionType::Value(USIZE_TYPE);
                  }
               }
               ExpressionType::Value(ValueType::CompileError) => {
                  lhs_type = ExpressionType::Value(ValueType::CompileError);
               }
               other_type => {
                  validation_context.error_count += 1;
                  writeln!(
                     err_stream,
                     "Encountered field access on type {}; only structs and arrays have fields",
                     other_type.as_roland_type_info(interner)
                  )
                  .unwrap();
                  emit_source_info(err_stream, expr_location, interner);
                  lhs_type = ExpressionType::Value(ValueType::CompileError);
               }
            }
            remaining_fields = if !remaining_fields.is_empty() {
               &remaining_fields[1..]
            } else {
               &[]
            };
         }
         lhs_type
      }
      Expression::ArrayLiteral(elems) => {
         for elem in elems.iter_mut() {
            type_expression(err_stream, *elem, validation_context, interner);
         }

         let mut any_error = false;

         for i in 1..elems.len() {
            try_set_inferred_type(
               &validation_context.expressions[elems[i - 1]].exp_type.clone().unwrap(),
               elems[i],
               validation_context,
               err_stream,
               interner,
            );

            let last_elem_expr = &validation_context.expressions[elems[i - 1]];
            let this_elem_expr = &validation_context.expressions[elems[i]];

            if last_elem_expr.exp_type.as_ref().unwrap().is_error_type()
               || this_elem_expr.exp_type.as_ref().unwrap().is_error_type()
            {
               // avoid cascading errors
               continue;
            } else if last_elem_expr.exp_type.as_ref().unwrap() != this_elem_expr.exp_type.as_ref().unwrap() {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Element at array index {} has type of {}, but element at array index {} has mismatching type of {}",
                  i - 1,
                  last_elem_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
                  i,
                  this_elem_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
               )
               .unwrap();
               emit_source_info_with_description(err_stream, expr_location, "array literal", interner);
               // @UnnecessaryAllocation
               let description = format!("element {}", i - 1);
               emit_source_info_with_description(err_stream, last_elem_expr.expression_begin_location, &description, interner);
               // @UnnecessaryAllocation
               let description = format!("element {}", i);
               emit_source_info_with_description(err_stream, this_elem_expr.expression_begin_location, &description, interner);
               any_error = true;
            }
         }

         // @FixedPointerWidth
         if elems.len() > std::u32::MAX as usize {
            any_error = true;
            writeln!(
               err_stream,
               "Array literal has {} elements, which is more than the maximum {} elements",
               elems.len(),
               // FixedPointerWidth
               std::u32::MAX,
            )
            .unwrap();
            emit_source_info(err_stream, expr_location, interner);
         }

         if any_error {
            ExpressionType::Value(ValueType::CompileError)
         } else if elems.is_empty() {
            ExpressionType::Value(ValueType::Array(
               Box::new(ExpressionType::Value(ValueType::Unit)),
               elems.len() as i128,
            ))
         } else {
            let a_type = validation_context.expressions[elems[0]].exp_type.clone().unwrap();

            ExpressionType::Value(ValueType::Array(Box::new(a_type), elems.len() as i128))
         }
      }
      Expression::ArrayIndex { array, index } => {
         type_expression(err_stream, *array, validation_context, interner);
         type_expression(err_stream, *index, validation_context, interner);

         try_set_inferred_type(
            &ExpressionType::Value(USIZE_TYPE),
            *index,
            validation_context,
            err_stream,
            interner,
         );

         let array_expression = &validation_context.expressions[*array];
         let index_expression = &validation_context.expressions[*index];

         if !index_expression.exp_type.as_ref().unwrap().is_concrete_type() {
            // avoid cascading errors
         } else if index_expression.exp_type.as_ref().unwrap() != &ExpressionType::Value(USIZE_TYPE) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Attempted to index an array with a value of type {}, which is not usize",
               index_expression
                  .exp_type
                  .as_ref()
                  .unwrap()
                  .as_roland_type_info(interner),
            )
            .unwrap();
            emit_source_info_with_description(err_stream, index_expression.expression_begin_location, "index", interner);
         }

         match &array_expression.exp_type {
            Some(ExpressionType::Value(ValueType::CompileError)) => ExpressionType::Value(ValueType::CompileError),
            Some(ExpressionType::Value(ValueType::Array(b, _))) => *b.clone(),
            Some(x) => {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Attempted to index expression of type {}, which is not an array type",
                  x.as_roland_type_info(interner),
               )
               .unwrap();
               emit_source_info_with_description(err_stream, array_expression.expression_begin_location, "expression", interner);
               emit_source_info_with_description(err_stream, index_expression.expression_begin_location, "index", interner);

               ExpressionType::Value(ValueType::CompileError)
            }
            None => unreachable!(),
         }
      }
      Expression::EnumLiteral(x, v) => {
         if let Some(enum_info) = validation_context.enum_info.get(x) {
            if enum_info.variants.contains(v) {
               ExpressionType::Value(ValueType::Enum(*x))
            } else {
               validation_context.error_count += 1;
               writeln!(
                  err_stream,
                  "Attempted to instantiate enum variant `{}` of enum `{}`, which is not a valid variant",
                  interner.lookup(*v),
                  interner.lookup(*x),
               )
               .unwrap();
               emit_source_info(err_stream, expr_location, interner);

               ExpressionType::Value(ValueType::CompileError)
            }
         } else {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Attempted to instantiate enum `{}`, which does not exist",
               interner.lookup(*x),
            )
            .unwrap();
            emit_source_info(err_stream, expr_location, interner);

            ExpressionType::Value(ValueType::CompileError)
         }
      }
   }
}

fn type_expression<W: Write>(
   err_stream: &mut W,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) {
   validation_context.expressions[expr_index].exp_type =
      Some(get_type(err_stream, expr_index, validation_context, interner));
}
