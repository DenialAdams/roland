use std::collections::{HashMap, HashSet};
use std::ops::BitOrAssign;

use indexmap::{IndexMap, IndexSet};

use super::{EnumInfo, GlobalInfo, GlobalKind, ProcedureInfo, StructInfo, UnionInfo};
use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_w_details};
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{ExpressionTypeNode, ProcImplSource, UserDefinedTypeInfo};
use crate::semantic_analysis::validator::resolve_type;
use crate::size_info::{calculate_struct_size_info, calculate_union_size_info};
use crate::source_info::{SourceInfo, SourcePath};
use crate::type_data::{ExpressionType, U16_TYPE, U32_TYPE, U64_TYPE, U8_TYPE};
use crate::{CompilationConfig, Program};

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

fn recursive_struct_union_check(
   base_name: StrId,
   seen_structs_or_unions: &mut HashSet<StrId>,
   struct_or_union_fields: &IndexMap<StrId, ExpressionTypeNode>,
   struct_info: &IndexMap<StrId, StructInfo>,
   union_info: &IndexMap<StrId, UnionInfo>,
) -> RecursiveStructCheckResult {
   let mut is_recursive = RecursiveStructCheckResult::NotRecursive;

   for struct_field in struct_or_union_fields.iter().flat_map(|x| match &x.1.e_type {
      ExpressionType::Struct(x) => Some(*x),
      ExpressionType::Union(x) => Some(*x),
      // Types should be fully resolved at this point, but may not be if there is an error in the program
      // (in that case, it's fine to ignore it as we'll already error out)
      ExpressionType::Unresolved(x) => Some(*x),
      _ => None,
   }) {
      if struct_field == base_name {
         is_recursive = RecursiveStructCheckResult::ContainsSelf;
         break;
      }

      if seen_structs_or_unions.contains(&struct_field) {
         is_recursive = RecursiveStructCheckResult::ContainsRecursiveStruct;
         continue;
      }

      seen_structs_or_unions.insert(struct_field);

      is_recursive |= struct_info
         .get(&struct_field)
         .map_or(RecursiveStructCheckResult::NotRecursive, |si| {
            recursive_struct_union_check(
               base_name,
               seen_structs_or_unions,
               &si.field_types,
               struct_info,
               union_info,
            )
         });

      is_recursive |= union_info
         .get(&struct_field)
         .map_or(RecursiveStructCheckResult::NotRecursive, |si| {
            recursive_struct_union_check(
               base_name,
               seen_structs_or_unions,
               &si.field_types,
               struct_info,
               union_info,
            )
         });
   }

   is_recursive
}

fn insert_or_error_duplicated(
   all_types: &mut HashMap<StrId, SourceInfo>,
   err_manager: &mut ErrorManager,
   name: StrId,
   location: SourceInfo,
   interner: &Interner,
) {
   if let Some(existing_declaration) = all_types.insert(name, location) {
      rolandc_error_w_details!(
         err_manager,
         &[
            (existing_declaration, "first type defined"),
            (location, "second type defined")
         ],
         "Encountered duplicate types with the same name `{}`",
         interner.lookup(name)
      );
   }
}

fn populate_user_defined_type_info(
   program: &mut Program,
   err_manager: &mut ErrorManager,
   interner: &Interner,
) -> UserDefinedTypeInfo {
   let mut udt = UserDefinedTypeInfo {
      enum_info: IndexMap::new(),
      struct_info: IndexMap::new(),
      union_info: IndexMap::new(),
   };

   let mut dupe_check = HashSet::new();
   let mut all_types = HashMap::new();

   for a_enum in program.enums.drain(..) {
      dupe_check.clear();
      for variant in a_enum.variants.iter() {
         if !dupe_check.insert(variant.str) {
            rolandc_error!(
               err_manager,
               a_enum.location,
               "Enum `{}` has a duplicate variant `{}`",
               interner.lookup(a_enum.name),
               interner.lookup(variant.str),
            );
         }
      }

      let base_type = if let Some(etn) = a_enum.requested_size.as_ref() {
         let base_type = match etn.e_type {
            U64_TYPE => U64_TYPE,
            U32_TYPE => {
               if a_enum.variants.len() > (u64::from(u32::MAX) + 1) as usize {
                  rolandc_error!(
                     err_manager,
                     etn.location,
                     "Enum `{}` has {} variants, which exceeds the maximum capacity of the specified base type ({})",
                     interner.lookup(a_enum.name),
                     a_enum.variants.len(),
                     u64::from(u32::MAX) + 1
                  );
               }
               U32_TYPE
            }
            U16_TYPE => {
               if a_enum.variants.len() > (u32::from(u16::MAX) + 1) as usize {
                  rolandc_error!(
                     err_manager,
                     etn.location,
                     "Enum `{}` has {} variants, which exceeds the maximum capacity of the specified base type ({})",
                     interner.lookup(a_enum.name),
                     a_enum.variants.len(),
                     u32::from(u16::MAX) + 1
                  );
               }
               U16_TYPE
            }
            U8_TYPE => {
               if a_enum.variants.len() > (u16::from(u8::MAX) + 1) as usize {
                  rolandc_error!(
                     err_manager,
                     etn.location,
                     "Enum `{}` has {} variants, which exceeds the maximum capacity of the specified base type ({})",
                     interner.lookup(a_enum.name),
                     a_enum.variants.len(),
                     u16::from(u8::MAX) + 1,
                  );
               }
               U8_TYPE
            }
            _ => {
               rolandc_error!(err_manager, etn.location, "Enum base type must be an unsigned integer");
               // We're opting to continue without defining the enum instead of setting a bogus size.
               // I'm not sure what's better for error behavior, but I just don't like assuming a size
               continue;
            }
         };
         if a_enum.variants.is_empty() {
            rolandc_error!(
               err_manager,
               etn.location,
               "Enum `{}` has no variants, so it must be zero sized and can't have a base type",
               interner.lookup(a_enum.name),
            );
         }
         base_type
      } else if a_enum.variants.len() > (u64::from(u32::MAX) + 1) as usize {
         U64_TYPE
      } else if a_enum.variants.len() > (u32::from(u16::MAX) + 1) as usize {
         U32_TYPE
      } else if a_enum.variants.len() > (u16::from(u8::MAX) + 1) as usize {
         U16_TYPE
      } else if !a_enum.variants.is_empty() {
         U8_TYPE
      } else {
         ExpressionType::Unit
      };

      insert_or_error_duplicated(&mut all_types, err_manager, a_enum.name, a_enum.location, interner);
      udt.enum_info.insert(
         a_enum.name,
         EnumInfo {
            variants: a_enum.variants.iter().map(|x| (x.str, x.location)).collect(),
            location: a_enum.location,
            base_type,
         },
      );
   }

   for a_struct in program.structs.drain(..) {
      let mut field_map = IndexMap::with_capacity(a_struct.fields.len());
      let mut default_value_map = IndexMap::with_capacity(a_struct.fields.len());

      for field in a_struct.fields.iter() {
         if field_map.insert(field.0, field.1.clone()).is_some() {
            rolandc_error!(
               err_manager,
               a_struct.location,
               "Struct `{}` has a duplicate field `{}`",
               interner.lookup(a_struct.name),
               interner.lookup(field.0),
            );
         }

         if let Some(expr_id) = field.2 {
            default_value_map.insert(field.0, expr_id);
         }
      }

      insert_or_error_duplicated(&mut all_types, err_manager, a_struct.name, a_struct.location, interner);
      udt.struct_info.insert(
         a_struct.name,
         StructInfo {
            field_types: field_map,
            default_values: default_value_map,
            location: a_struct.location,
            size: None,
         },
      );
   }

   for a_union in program.unions.drain(..) {
      let mut field_map = IndexMap::with_capacity(a_union.fields.len());

      for field in a_union.fields.iter() {
         if field_map.insert(field.0, field.1.clone()).is_some() {
            rolandc_error!(
               err_manager,
               a_union.location,
               "Union `{}` has a duplicate field `{}`",
               interner.lookup(a_union.name),
               interner.lookup(field.0),
            );
         }
      }

      insert_or_error_duplicated(&mut all_types, err_manager, a_union.name, a_union.location, interner);
      udt.union_info.insert(
         a_union.name,
         UnionInfo {
            field_types: field_map,
            location: a_union.location,
            size: None,
         },
      );
   }

   // nocheckin the clone is downright silly now
   let cloned_udt = udt.clone();
   for struct_i in udt.struct_info.iter_mut() {
      for (field, etn) in struct_i.1.field_types.iter_mut() {
         if resolve_type(&mut etn.e_type, &cloned_udt, None).is_ok() {
            continue;
         }

         let etype_str = etn.e_type.as_roland_type_info_notv(interner, &program.procedure_info);
         rolandc_error_w_details!(
            err_manager,
            &[(struct_i.1.location, "struct defined")],
            "Field `{}` of struct `{}` is of undeclared type `{}`",
            interner.lookup(*field),
            interner.lookup(*struct_i.0),
            etype_str,
         );
      }
   }

   udt
}

pub fn populate_type_and_procedure_info(
   program: &mut Program,
   err_manager: &mut ErrorManager,
   interner: &Interner,
   config: &CompilationConfig,
) {
   program.user_defined_types = populate_user_defined_type_info(program, err_manager, interner);

   // Check for recursive structs only after we've attempted to resolve all of the field types
   let mut seen_structs_or_unions = HashSet::new();
   for struct_i in program.user_defined_types.struct_info.iter() {
      seen_structs_or_unions.clear();
      if recursive_struct_union_check(
         *struct_i.0,
         &mut seen_structs_or_unions,
         &struct_i.1.field_types,
         &program.user_defined_types.struct_info,
         &program.user_defined_types.union_info,
      ) == RecursiveStructCheckResult::ContainsSelf
      {
         rolandc_error!(
            err_manager,
            struct_i.1.location,
            "Struct `{}` contains itself, which isn't allowed as it would result in an infinitely large struct",
            interner.lookup(*struct_i.0),
         );
      }
   }

   for union_i in program.user_defined_types.union_info.iter() {
      seen_structs_or_unions.clear();
      if recursive_struct_union_check(
         *union_i.0,
         &mut seen_structs_or_unions,
         &union_i.1.field_types,
         &program.user_defined_types.struct_info,
         &program.user_defined_types.union_info,
      ) == RecursiveStructCheckResult::ContainsSelf
      {
         rolandc_error!(
            err_manager,
            union_i.1.location,
            "Union `{}` contains itself, which isn't allowed as it would result in an infinitely large struct",
            interner.lookup(*union_i.0),
         );
      }
   }

   for const_node in program.consts.iter_mut() {
      let const_type = &mut const_node.const_type.e_type;
      let si = &const_node.location;

      if resolve_type(const_type, &program.user_defined_types, None).is_err() {
         let static_type_str = const_type.as_roland_type_info_notv(interner, &program.procedure_info);
         rolandc_error!(
            err_manager,
            const_node.const_type.location,
            "Const `{}` is of undeclared type `{}`",
            interner.lookup(const_node.name.str),
            static_type_str,
         );
      }

      if let Some(old_value) = program.global_info.insert(
         program.next_variable,
         GlobalInfo {
            expr_type: const_node.const_type.clone(),
            initializer: Some(const_node.value),
            location: const_node.location,
            kind: GlobalKind::Const,
            name: const_node.name.str,
         },
      ) {
         rolandc_error_w_details!(
            err_manager,
            &[
               (old_value.location, "first static/const defined"),
               (*si, "second static/const defined"),
            ],
            "Encountered duplicate static/const with the same name `{}`",
            interner.lookup(const_node.name.str),
         );
      }
      const_node.var_id = program.next_variable;
      program.next_variable = program.next_variable.next();
   }

   for mut static_node in program.statics.drain(..) {
      if resolve_type(&mut static_node.static_type.e_type, &program.user_defined_types, None).is_err() {
         let static_type_str = static_node
            .static_type
            .e_type
            .as_roland_type_info_notv(interner, &program.procedure_info);
         rolandc_error!(
            err_manager,
            static_node.static_type.location,
            "Static `{}` is of undeclared type `{}`",
            interner.lookup(static_node.name.str),
            static_type_str,
         );
      }

      if let Some(old_value) = program.global_info.insert(
         program.next_variable,
         GlobalInfo {
            expr_type: static_node.static_type,
            initializer: static_node.value,
            location: static_node.location,
            kind: GlobalKind::Static,
            name: static_node.name.str,
         },
      ) {
         rolandc_error_w_details!(
            err_manager,
            &[
               (old_value.location, "first static/const defined"),
               (static_node.location, "second static/const defined")
            ],
            "Encountered duplicate static/const with the same name `{}`",
            interner.lookup(static_node.name.str),
         );
      }
      program.next_variable = program.next_variable.next();
   }

   let mut dupe_check = HashSet::new();
   for (id, definition, source_location, proc_impl_source) in program
      .procedures
      .iter_mut()
      .map(|(id, x)| (id, &mut x.definition, x.location, &x.proc_impl))
   {
      dupe_check.clear();

      if matches!(proc_impl_source, ProcImplSource::Builtin) && !source_is_std(source_location, config) {
         rolandc_error!(
            err_manager,
            source_location,
            "Procedure `{}` is declared to be builtin, but only the compiler can declare builtin procedures",
            interner.lookup(definition.name.str),
         );
      }

      let mut first_named_param = None;
      let mut reported_named_error = false;
      for (i, param) in definition.parameters.iter().enumerate() {
         if !dupe_check.insert(param.name) {
            rolandc_error!(
               err_manager,
               source_location,
               "Procedure `{}` has a duplicate parameter `{}`",
               interner.lookup(definition.name.str),
               interner.lookup(param.name),
            );
         }

         if param.named && first_named_param.is_none() {
            first_named_param = Some(i);

            if matches!(proc_impl_source, ProcImplSource::External) {
               reported_named_error = true;
               rolandc_error!(
                  err_manager,
                  source_location,
                  "External procedure `{}` has named parameter(s), which isn't supported",
                  interner.lookup(definition.name.str),
               );
            }
         }

         if !param.named && first_named_param.is_some() && !reported_named_error {
            reported_named_error = true;
            rolandc_error!(
               err_manager,
               source_location,
               "Procedure `{}` has named parameter(s) which come before non-named parameter(s)",
               interner.lookup(definition.name.str),
            );
         }
      }

      if !reported_named_error && first_named_param.is_some() {
         if let Some(i) = first_named_param {
            // It doesn't really matter how we sort these, as long as we do it consistently for arguments
            // AND that there are no equal elements (in this case, we already check that parameters don't have the same name)
            definition.parameters[i..].sort_unstable_by_key(|x| x.name);
         }
      }

      for constraint in definition.constraints.iter() {
         let matching_generic_param = match definition.generic_parameters.iter().find(|x| x.str == *constraint.0) {
            Some(x) => x.str,
            None => {
               rolandc_error!(
                  err_manager,
                  source_location,
                  "A constraint was declared on {}, but there is no matching generic parameter by that name",
                  interner.lookup(*constraint.0),
               );
               continue;
            }
         };

         for constraint_trait_name in constraint.1.iter() {
            match interner.lookup(*constraint_trait_name) {
               "Enum" => (),
               "Float" => (),
               _ => {
                  rolandc_error!(
                     err_manager,
                     source_location,
                     "Unknown trait {} was declared as a constraint on {}",
                     interner.lookup(*constraint_trait_name),
                     interner.lookup(matching_generic_param),
                  );
               }
            }
         }
      }

      let type_parameters_with_constraints: IndexMap<StrId, IndexSet<StrId>> = definition
         .generic_parameters
         .iter()
         .map(|x| {
            (
               x.str,
               definition
                  .constraints
                  .get_mut(&x.str)
                  .map_or_else(IndexSet::new, |x| std::mem::replace(x, IndexSet::new())),
            )
         })
         .collect();

      for parameter in definition.parameters.iter_mut() {
         if resolve_type(
            &mut parameter.p_type.e_type,
            &program.user_defined_types,
            Some(&type_parameters_with_constraints),
         )
         .is_err()
         {
            let etype_str = parameter
               .p_type
               .e_type
               .as_roland_type_info_notv(interner, &program.procedure_info);
            rolandc_error!(
               err_manager,
               parameter.p_type.location,
               "Parameter `{}` of procedure `{}` is of undeclared type `{}`",
               interner.lookup(parameter.name),
               interner.lookup(definition.name.str),
               etype_str,
            );
         }
      }

      if resolve_type(
         &mut definition.ret_type.e_type,
         &program.user_defined_types,
         Some(&type_parameters_with_constraints),
      )
      .is_err()
      {
         let etype_str = definition
            .ret_type
            .e_type
            .as_roland_type_info_notv(interner, &program.procedure_info);
         rolandc_error!(
            err_manager,
            definition.ret_type.location,
            "Return type of procedure `{}` is of undeclared type `{}`",
            interner.lookup(definition.name.str),
            etype_str,
         );
      }

      program.procedure_info.insert(
         id,
         ProcedureInfo {
            type_parameters: type_parameters_with_constraints,
            parameters: definition.parameters.iter().map(|x| x.p_type.e_type.clone()).collect(),
            named_parameters: definition
               .parameters
               .iter()
               .filter(|x| x.named)
               .map(|x| (x.name, x.p_type.e_type.clone()))
               .collect(),
            ret_type: definition.ret_type.e_type.clone(),
            location: source_location,
            name: definition.name.clone(),
            is_builtin: matches!(proc_impl_source, ProcImplSource::Builtin),
         },
      );

      if let Some(old_proc_id) = program.procedure_name_table.insert(definition.name.str, id) {
         let old_proc_location = program.procedure_info[old_proc_id].location;
         rolandc_error_w_details!(
            err_manager,
            &[
               (old_proc_location, "first procedure declared"),
               (source_location, "second procedure declared")
            ],
            "Encountered duplicate procedures with the same name `{}`",
            interner.lookup(definition.name.str),
         );
      }
   }

   // We must return now before calculating sizes
   // (or we'll blow up on recursive types)
   if !err_manager.errors.is_empty() {
      return;
   }

   for i in 0..program.user_defined_types.struct_info.len() {
      let s = program.user_defined_types.struct_info.get_index(i).unwrap().0;
      calculate_struct_size_info(*s, &mut program.user_defined_types);
   }

   for i in 0..program.user_defined_types.union_info.len() {
      let s = program.user_defined_types.union_info.get_index(i).unwrap().0;
      calculate_union_size_info(*s, &mut program.user_defined_types);
   }
}

fn source_is_std(source_location: SourceInfo, config: &CompilationConfig) -> bool {
   matches!(source_location.file, SourcePath::Std(_)) || config.i_am_std
}
