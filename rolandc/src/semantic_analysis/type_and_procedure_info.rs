use std::collections::{HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};
use slotmap::{SecondaryMap, SlotMap};

use super::validator::str_to_builtin_type;
use super::{EnumInfo, GlobalInfo, GlobalKind, StructInfo, UnionInfo};
use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_w_details};
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{EnumId, ExpressionTypeNode, ProcImplSource, StructId, UnionId, UserDefinedTypeId};
use crate::semantic_analysis::validator::resolve_type;
use crate::size_info::{calculate_struct_size_info, calculate_union_size_info};
use crate::source_info::{SourceInfo, SourcePath};
use crate::type_data::{ExpressionType, U16_TYPE, U32_TYPE, U64_TYPE, U8_TYPE};
use crate::{CompilationConfig, Program};

fn recursive_struct_union_check(
   base_id: UserDefinedTypeId,
   seen_structs_or_unions: &mut HashSet<UserDefinedTypeId>,
   struct_or_union_fields: &IndexMap<StrId, ExpressionTypeNode>,
   struct_info: &SlotMap<StructId, StructInfo>,
   union_info: &SlotMap<UnionId, UnionInfo>,
) -> bool {
   let mut is_recursive = false;

   for field in struct_or_union_fields.iter() {
      match &field.1.e_type {
         ExpressionType::Struct(x) => {
            if UserDefinedTypeId::Struct(*x) == base_id {
               is_recursive = true;
               break;
            }

            if !seen_structs_or_unions.insert(UserDefinedTypeId::Struct(*x)) {
               continue;
            }

            is_recursive |= recursive_struct_union_check(
               base_id,
               seen_structs_or_unions,
               &struct_info.get(*x).unwrap().field_types,
               struct_info,
               union_info,
            );
         }
         ExpressionType::Union(x) => {
            if UserDefinedTypeId::Union(*x) == base_id {
               is_recursive = true;
               break;
            }

            if !seen_structs_or_unions.insert(UserDefinedTypeId::Union(*x)) {
               continue;
            }

            is_recursive |= recursive_struct_union_check(
               base_id,
               seen_structs_or_unions,
               &union_info.get(*x).unwrap().field_types,
               struct_info,
               union_info,
            );
         }
         _ => continue,
      }
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
   let name_str = interner.lookup(name);
   if str_to_builtin_type(name_str).is_some() {
      rolandc_error!(err_manager, location, "`{}` is a builtin type", name_str);
   } else if let Some(existing_declaration) = all_types.insert(name, location) {
      rolandc_error_w_details!(
         err_manager,
         &[
            (existing_declaration, "first type defined"),
            (location, "second type defined")
         ],
         "Encountered duplicate types with the same name `{}`",
         name_str
      );
   }
}

fn populate_user_defined_type_info(program: &mut Program, err_manager: &mut ErrorManager, interner: &Interner) {
   let mut dupe_check = HashSet::new();
   let mut all_types = HashMap::new();

   let mut enum_base_type_locations: SecondaryMap<EnumId, SourceInfo> = SecondaryMap::new();
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

      let (base_type, btl) = if let Some(etn) = a_enum.requested_size {
         // We'll resolve this type after all preliminary type info has been populated
         (etn.e_type, etn.location)
      } else if a_enum.variants.len() > (u64::from(u32::MAX) + 1) as usize {
         (U64_TYPE, a_enum.location)
      } else if a_enum.variants.len() > (u32::from(u16::MAX) + 1) as usize {
         (U32_TYPE, a_enum.location)
      } else if a_enum.variants.len() > (u16::from(u8::MAX) + 1) as usize {
         (U16_TYPE, a_enum.location)
      } else if !a_enum.variants.is_empty() {
         (U8_TYPE, a_enum.location)
      } else {
         (ExpressionType::Unit, a_enum.location)
      };

      insert_or_error_duplicated(&mut all_types, err_manager, a_enum.name, a_enum.location, interner);
      let enum_id = program.user_defined_types.enum_info.insert(EnumInfo {
         variants: a_enum.variants.iter().map(|x| (x.str, x.location)).collect(),
         location: a_enum.location,
         name: a_enum.name,
         base_type,
      });
      program
         .user_defined_type_name_table
         .insert(a_enum.name, UserDefinedTypeId::Enum(enum_id));
      enum_base_type_locations.insert(enum_id, btl);
   }

   for a_struct in program.structs.drain(..) {
      let mut field_map = IndexMap::with_capacity(a_struct.fields.len());

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
      }

      insert_or_error_duplicated(&mut all_types, err_manager, a_struct.name, a_struct.location, interner);
      let struct_id = program.user_defined_types.struct_info.insert(StructInfo {
         field_types: field_map,
         location: a_struct.location,
         size: None,
         name: a_struct.name,
      });
      program
         .user_defined_type_name_table
         .insert(a_struct.name, UserDefinedTypeId::Struct(struct_id));
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
      let union_id = program.user_defined_types.union_info.insert(UnionInfo {
         field_types: field_map,
         location: a_union.location,
         size: None,
         name: a_union.name,
      });
      program
         .user_defined_type_name_table
         .insert(a_union.name, UserDefinedTypeId::Union(union_id));
   }

   for (id, enum_i) in program.user_defined_types.enum_info.iter_mut() {
      let base_type_location = enum_base_type_locations[id];

      if !resolve_type(
         &mut enum_i.base_type,
         &program.user_defined_type_name_table,
         None,
         err_manager,
         interner,
         base_type_location,
      ) {
         continue;
      };

      match enum_i.base_type {
         U64_TYPE => (),
         U32_TYPE => {
            if enum_i.variants.len() > (u64::from(u32::MAX) + 1) as usize {
               rolandc_error!(
                  err_manager,
                  base_type_location,
                  "Enum `{}` has {} variants, which exceeds the maximum capacity of the specified base type ({})",
                  interner.lookup(enum_i.name),
                  enum_i.variants.len(),
                  u64::from(u32::MAX) + 1
               );
            }
         }
         U16_TYPE => {
            if enum_i.variants.len() > (u32::from(u16::MAX) + 1) as usize {
               rolandc_error!(
                  err_manager,
                  base_type_location,
                  "Enum `{}` has {} variants, which exceeds the maximum capacity of the specified base type ({})",
                  interner.lookup(enum_i.name),
                  enum_i.variants.len(),
                  u32::from(u16::MAX) + 1
               );
            }
         }
         U8_TYPE => {
            if enum_i.variants.len() > (u16::from(u8::MAX) + 1) as usize {
               rolandc_error!(
                  err_manager,
                  base_type_location,
                  "Enum `{}` has {} variants, which exceeds the maximum capacity of the specified base type ({})",
                  interner.lookup(enum_i.name),
                  enum_i.variants.len(),
                  u16::from(u8::MAX) + 1,
               );
            }
         }
         ExpressionType::Unit => {
            if !enum_i.variants.is_empty() {
               rolandc_error!(
                  err_manager,
                  base_type_location,
                  "Enum `{}` has {} variants, which exceeds the maximum capacity of the specified base type ({})",
                  interner.lookup(enum_i.name),
                  enum_i.variants.len(),
                  0,
               );
            }
         }
         _ => {
            rolandc_error!(
               err_manager,
               base_type_location,
               "Enum base type must be an unsigned integer"
            );
         }
      }
   }
   for struct_i in program.user_defined_types.struct_info.values_mut() {
      for etn in struct_i.field_types.values_mut() {
         resolve_type(
            &mut etn.e_type,
            &program.user_defined_type_name_table,
            None,
            err_manager,
            interner,
            etn.location,
         );
      }
   }
   for union_i in program.user_defined_types.union_info.values_mut() {
      for etn in union_i.field_types.values_mut() {
         resolve_type(
            &mut etn.e_type,
            &program.user_defined_type_name_table,
            None,
            err_manager,
            interner,
            etn.location,
         );
      }
   }
}

pub fn populate_type_and_procedure_info(
   program: &mut Program,
   err_manager: &mut ErrorManager,
   interner: &Interner,
   config: &CompilationConfig,
) {
   populate_user_defined_type_info(program, err_manager, interner);

   // Check for recursive structs only after we've attempted to resolve all of the field types
   let mut seen_structs_or_unions = HashSet::new();
   for struct_i in program.user_defined_types.struct_info.iter() {
      seen_structs_or_unions.clear();
      if recursive_struct_union_check(
         UserDefinedTypeId::Struct(struct_i.0),
         &mut seen_structs_or_unions,
         &struct_i.1.field_types,
         &program.user_defined_types.struct_info,
         &program.user_defined_types.union_info,
      ) {
         rolandc_error!(
            err_manager,
            struct_i.1.location,
            "Struct `{}` contains itself, which isn't allowed as it would result in an infinitely large struct",
            interner.lookup(struct_i.1.name),
         );
      }
   }

   for union_i in program.user_defined_types.union_info.iter() {
      seen_structs_or_unions.clear();
      if recursive_struct_union_check(
         UserDefinedTypeId::Union(union_i.0),
         &mut seen_structs_or_unions,
         &union_i.1.field_types,
         &program.user_defined_types.struct_info,
         &program.user_defined_types.union_info,
      ) {
         rolandc_error!(
            err_manager,
            union_i.1.location,
            "Union `{}` contains itself, which isn't allowed as it would result in an infinitely large union",
            interner.lookup(union_i.1.name),
         );
      }
   }

   for mut const_node in program.consts.drain(..) {
      resolve_type(
         &mut const_node.const_type.e_type,
         &program.user_defined_type_name_table,
         None,
         err_manager,
         interner,
         const_node.const_type.location,
      );

      if let Some(old_value) = program.global_info.insert(
         program.next_variable,
         GlobalInfo {
            expr_type: const_node.const_type,
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
               (const_node.location, "second static/const defined"),
            ],
            "Encountered duplicate static/const with the same name `{}`",
            interner.lookup(const_node.name.str),
         );
      }
      program.next_variable = program.next_variable.next();
   }

   for mut static_node in program.statics.drain(..) {
      resolve_type(
         &mut static_node.static_type.e_type,
         &program.user_defined_type_name_table,
         None,
         err_manager,
         interner,
         static_node.static_type.location,
      );

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
   for proc in program.procedures.values_mut() {
      dupe_check.clear();

      if proc.impl_source == ProcImplSource::Builtin && !source_is_std(proc.location, config) {
         rolandc_error!(
            err_manager,
            proc.location,
            "Procedure `{}` is declared to be builtin, but only the compiler can declare builtin procedures",
            interner.lookup(proc.definition.name.str),
         );
      }

      let mut first_named_param = None;
      let mut reported_named_error = false;
      for (i, param) in proc.definition.parameters.iter().enumerate() {
         if !dupe_check.insert(param.name) {
            rolandc_error!(
               err_manager,
               proc.location,
               "Procedure `{}` has a duplicate parameter `{}`",
               interner.lookup(proc.definition.name.str),
               interner.lookup(param.name),
            );
         }

         if param.named && first_named_param.is_none() {
            first_named_param = Some(i);

            if proc.impl_source == ProcImplSource::External {
               reported_named_error = true;
               rolandc_error!(
                  err_manager,
                  proc.location,
                  "External procedure `{}` has named parameter(s), which isn't supported",
                  interner.lookup(proc.definition.name.str),
               );
            }
         }

         if !param.named && first_named_param.is_some() && !reported_named_error {
            reported_named_error = true;
            rolandc_error!(
               err_manager,
               proc.location,
               "Procedure `{}` has named parameter(s) which come before non-named parameter(s)",
               interner.lookup(proc.definition.name.str),
            );
         }
      }

      if !reported_named_error && first_named_param.is_some() {
         if let Some(i) = first_named_param {
            // It doesn't really matter how we sort these, as long as we do it consistently for arguments
            // AND that there are no equal elements (in this case, we already check that parameters don't have the same name)
            proc.definition.parameters[i..].sort_unstable_by_key(|x| x.name);
         }
      }

      dupe_check.clear();
      for generic_param in proc.definition.type_parameters.iter() {
         if !dupe_check.insert(generic_param.str) {
            rolandc_error!(
               err_manager,
               generic_param.location,
               "Procedure `{}` has a duplicate type parameter `{}`",
               interner.lookup(proc.definition.name.str),
               interner.lookup(generic_param.str),
            );
         }
      }

      for constraint in proc.definition.constraints.iter() {
         let matching_generic_param = match proc.definition.type_parameters.iter().find(|x| x.str == *constraint.0) {
            Some(x) => x.str,
            None => {
               rolandc_error!(
                  err_manager,
                  proc.location,
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
                     proc.location,
                     "Unknown trait {} was declared as a constraint on {}",
                     interner.lookup(*constraint_trait_name),
                     interner.lookup(matching_generic_param),
                  );
               }
            }
         }
      }

      let type_parameters_with_constraints: IndexMap<StrId, IndexSet<StrId>> = proc
         .definition
         .type_parameters
         .iter()
         .map(|x| {
            (
               x.str,
               proc
                  .definition
                  .constraints
                  .get_mut(&x.str)
                  .map_or_else(IndexSet::new, |x| std::mem::replace(x, IndexSet::new())),
            )
         })
         .collect();

      for parameter in proc.definition.parameters.iter_mut() {
         resolve_type(
            &mut parameter.p_type.e_type,
            &program.user_defined_type_name_table,
            Some(&type_parameters_with_constraints),
            err_manager,
            interner,
            parameter.p_type.location,
         );
      }

      resolve_type(
         &mut proc.definition.ret_type.e_type,
         &program.user_defined_type_name_table,
         Some(&type_parameters_with_constraints),
         err_manager,
         interner,
         proc.definition.ret_type.location,
      );

      proc.type_parameters = type_parameters_with_constraints;
      proc.named_parameters = proc
         .definition
         .parameters
         .iter()
         .filter(|x| x.named)
         .map(|x| (x.name, x.p_type.e_type.clone()))
         .collect();
   }

   for (id, proc_name, source_location) in program
      .procedures
      .iter()
      .map(|x| (x.0, x.1.definition.name.str, x.1.location))
   {
      if let Some(old_proc_id) = program.procedure_name_table.insert(proc_name, id) {
         let old_proc_location = program.procedures[old_proc_id].location;
         rolandc_error_w_details!(
            err_manager,
            &[
               (old_proc_location, "first procedure declared"),
               (source_location, "second procedure declared")
            ],
            "Encountered duplicate procedures with the same name `{}`",
            interner.lookup(proc_name),
         );
      }
   }

   // We must return now before calculating sizes
   // (or we'll blow up on recursive types)
   if !err_manager.errors.is_empty() {
      return;
   }

   let ids: Vec<StructId> = program.user_defined_types.struct_info.keys().collect();
   for id in ids {
      calculate_struct_size_info(id, &mut program.user_defined_types, config.target);
   }

   let ids: Vec<UnionId> = program.user_defined_types.union_info.keys().collect();
   for id in ids {
      calculate_union_size_info(id, &mut program.user_defined_types, config.target);
   }
}

fn source_is_std(source_location: SourceInfo, config: &CompilationConfig) -> bool {
   matches!(source_location.file, SourcePath::Std(_)) || config.i_am_std
}
