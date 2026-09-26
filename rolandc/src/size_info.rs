use std::collections::HashMap;

use indexmap::IndexSet;

use crate::error_handling::ErrorManager;
use crate::error_handling::error_handling_macros::rolandc_error;
use crate::interner::{Interner, StrId};
use crate::parse::{StructId, UnionId, UserDefinedTypeId, UserDefinedTypeInfo};
use crate::semantic_analysis::validator::map_generic_to_concrete_cow;
use crate::type_data::{ExpressionType, FloatWidth, IntWidth};
use crate::{BaseTarget, Target};

#[derive(Clone)]
pub struct StructSizeInfo {
   pub mem_size: u64,
   pub strictest_alignment: u64,
   pub field_offsets_mem: HashMap<StrId, u64>,
}

#[derive(Clone)]
pub struct UnionSizeInfo {
   pub mem_size: u64,
   pub mem_alignment: u64,
}

pub fn aligned_address(v: u64, a: u64) -> Option<u64> {
   let rem = v % a;
   if rem == 0 { Some(v) } else { v.checked_add(a - rem) }
}

fn ensure_type_already_processed(
   t: &ExpressionType,
   udt: &mut UserDefinedTypeInfo,
   target: Target,
   templated_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
   err_manager: &mut ErrorManager,
   interner: &Interner,
) {
   match t {
      ExpressionType::Struct(s, type_args) => {
         for type_arg in type_args.iter() {
            ensure_type_already_processed(type_arg, udt, target, templated_types, err_manager, interner);
         }
         calculate_struct_size_info(*s, udt, target, templated_types, err_manager, interner);
      }
      ExpressionType::Union(s, type_args) => {
         for type_arg in type_args.iter() {
            ensure_type_already_processed(type_arg, udt, target, templated_types, err_manager, interner);
         }
         calculate_union_size_info(*s, udt, target, templated_types, err_manager, interner);
      }
      ExpressionType::Array(bt, _) => {
         ensure_type_already_processed(bt, udt, target, templated_types, err_manager, interner);
      }
      _ => (),
   }
}

pub fn calculate_union_size_info(
   id: UnionId,
   udt: &mut UserDefinedTypeInfo,
   target: Target,
   templated_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
   err_manager: &mut ErrorManager,
   interner: &Interner,
) {
   if udt.union_info.get(id).unwrap().size.is_some() {
      return;
   }

   if templated_types.contains_key(&UserDefinedTypeId::Union(id)) {
      return;
   }

   let ft = std::mem::take(&mut udt.union_info.get_mut(id).unwrap().field_types);
   for field_t in ft.values() {
      ensure_type_already_processed(&field_t.e_type, udt, target, templated_types, err_manager, interner);
   }
   udt.union_info.get_mut(id).unwrap().field_types = ft;

   let (mem_size, mem_alignment) = {
      let mut our_mem_size = Some(0);
      let mut our_mem_alignment = 1;
      for field_t in udt.union_info.get(id).unwrap().field_types.values() {
         let field_t = &field_t.e_type;

         our_mem_size = our_mem_size.and_then(|v| {
            Some(std::cmp::max(
               v,
               template_type_aware_mem_size(field_t, udt, target.base(), templated_types)?,
            ))
         });
         our_mem_alignment = std::cmp::max(
            our_mem_alignment,
            template_type_aware_mem_alignment(field_t, udt, target.base(), templated_types),
         );
      }

      (
         our_mem_size.and_then(|v| aligned_address(v, our_mem_alignment)),
         our_mem_alignment,
      )
   };

   if mem_size.is_none() || mem_size.unwrap() > target.base().max_size() {
      rolandc_error!(
         err_manager,
         udt.union_info[id].location,
         "Union `{}` is too big for this target ({})",
         interner.lookup(udt.union_info[id].name),
         target
      );
   }

   udt.union_info.get_mut(id).unwrap().size = Some(UnionSizeInfo {
      mem_size: mem_size.unwrap_or(0),
      mem_alignment,
   });
}

pub fn calculate_struct_size_info(
   id: StructId,
   udt: &mut UserDefinedTypeInfo,
   target: Target,
   templated_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
   err_manager: &mut ErrorManager,
   interner: &Interner,
) {
   if udt.struct_info.get(id).unwrap().size.is_some() {
      return;
   }

   if templated_types.contains_key(&UserDefinedTypeId::Struct(id)) {
      return;
   }

   let ft = std::mem::take(&mut udt.struct_info.get_mut(id).unwrap().field_types);
   for field_t in ft.values() {
      ensure_type_already_processed(&field_t.e_type, udt, target, templated_types, err_manager, interner);
   }
   udt.struct_info.get_mut(id).unwrap().field_types = ft;

   let (mem_size, strictest_alignment, field_offsets_mem) = {
      let mut sum_mem = Some(0u64);
      let mut strictest_alignment = 1;
      let mut field_offsets_mem = HashMap::with_capacity(udt.struct_info.get(id).unwrap().field_types.len());
      for ((field_name, field_t), next_field_t) in udt.struct_info.get(id).unwrap().field_types.iter().zip(
         udt.struct_info
            .get(id)
            .unwrap()
            .field_types
            .values()
            .skip(1)
            .map(Some)
            .chain(std::iter::once(None)),
      ) {
         let field_t = &field_t.e_type;

         field_offsets_mem.insert(*field_name, sum_mem.unwrap_or(0));

         let next_mem_alignment = next_field_t.map_or(1, |x| {
            template_type_aware_mem_alignment(&x.e_type, udt, target.base(), templated_types)
         });
         sum_mem = sum_mem
            .and_then(|v| {
               v.checked_add(template_type_aware_mem_size(
                  field_t,
                  udt,
                  target.base(),
                  templated_types,
               )?)
            })
            .and_then(|v| aligned_address(v, next_mem_alignment));

         strictest_alignment = std::cmp::max(
            strictest_alignment,
            template_type_aware_mem_alignment(field_t, udt, target.base(), templated_types),
         );
      }

      (
         sum_mem.and_then(|v| aligned_address(v, strictest_alignment)),
         strictest_alignment,
         field_offsets_mem,
      )
   };

   if mem_size.is_none() || mem_size.unwrap() > target.base().max_size() {
      rolandc_error!(
         err_manager,
         udt.struct_info[id].location,
         "Struct `{}` is too big for this target ({})",
         interner.lookup(udt.struct_info[id].name),
         target
      );
   }

   udt.struct_info.get_mut(id).unwrap().size = Some(StructSizeInfo {
      mem_size: mem_size.unwrap_or(0),
      strictest_alignment,
      field_offsets_mem,
   });
}

pub fn template_type_aware_mem_alignment(
   e: &ExpressionType,
   udt: &UserDefinedTypeInfo,
   target: BaseTarget,
   templated_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
) -> u64 {
   match e {
      ExpressionType::Array(a_type, _len) => template_type_aware_mem_alignment(a_type, udt, target, templated_types),
      ExpressionType::Union(union_id, generic_args) => {
         if generic_args.is_empty() {
            mem_alignment(e, udt, target)
         } else {
            udt.union_info[*union_id]
               .field_types
               .values()
               .map(|x| {
                  map_generic_to_concrete_cow(
                     &x.e_type,
                     generic_args,
                     &templated_types[&UserDefinedTypeId::Union(*union_id)],
                  )
               })
               .map(|x| template_type_aware_mem_alignment(&x, udt, target, templated_types))
               .max()
               .unwrap_or(1)
         }
      }
      ExpressionType::Struct(struct_id, generic_args) => {
         if generic_args.is_empty() {
            mem_alignment(e, udt, target)
         } else {
            udt.struct_info[*struct_id]
               .field_types
               .values()
               .map(|x| {
                  map_generic_to_concrete_cow(
                     &x.e_type,
                     generic_args,
                     &templated_types[&UserDefinedTypeId::Struct(*struct_id)],
                  )
               })
               .map(|x| template_type_aware_mem_alignment(&x, udt, target, templated_types))
               .max()
               .unwrap_or(1)
         }
      }
      _ => mem_alignment(e, udt, target),
   }
}

pub fn mem_alignment(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: BaseTarget) -> u64 {
   match e {
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         mem_alignment(&base_type.e_type, udt, target)
      }
      ExpressionType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         IntWidth::Pointer => u64::from(target.pointer_width()),
         IntWidth::Four => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      },
      ExpressionType::Float(x) => match x.width {
         FloatWidth::Eight => 8,
         FloatWidth::Four => 4,
      },
      ExpressionType::Pointer(_) | ExpressionType::ProcedurePointer { .. } => u64::from(target.pointer_width()),
      ExpressionType::Struct(x, type_args) => {
         debug_assert!(type_args.is_empty());
         udt.struct_info
            .get(*x)
            .unwrap()
            .size
            .as_ref()
            .unwrap()
            .strictest_alignment
      }
      ExpressionType::Array(a_type, _len) => mem_alignment(a_type, udt, target),
      ExpressionType::Union(x, type_args) => {
         debug_assert!(type_args.is_empty());
         udt.union_info.get(*x).unwrap().size.as_ref().unwrap().mem_alignment
      }
      ExpressionType::Bool | ExpressionType::Unit | ExpressionType::Never | ExpressionType::ProcedureItem(_, _) => 1,
      ExpressionType::Unresolved { .. }
      | ExpressionType::Unknown(_)
      | ExpressionType::CompileError
      | ExpressionType::GenericParam(_) => unreachable!(),
   }
}

/// The size of a type, in number of WASM values
pub fn sizeof_type_values(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: BaseTarget) -> u32 {
   if sizeof_type_mem(e, udt, target) == 0 {
      return 0;
   }

   match e {
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         sizeof_type_values(&base_type.e_type, udt, target)
      }
      ExpressionType::Int(_)
      | ExpressionType::Float(_)
      | ExpressionType::Pointer(_)
      | ExpressionType::Bool
      | ExpressionType::Struct(_, _)
      | ExpressionType::Array(_, _)
      | ExpressionType::ProcedurePointer { .. }
      | ExpressionType::Union(_, _) => 1,
      ExpressionType::ProcedureItem(_, _) | ExpressionType::Unit | ExpressionType::Never => 0,
      ExpressionType::GenericParam(_)
      | ExpressionType::CompileError
      | ExpressionType::Unresolved { .. }
      | ExpressionType::Unknown(_) => unreachable!(),
   }
}

/// The size of a type, in bytes, as it's stored in local memory (minimum size 4 bytes)
pub fn sizeof_type_wasm(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: BaseTarget) -> u64 {
   let size_mem = sizeof_type_mem(e, udt, target);
   if size_mem == 0 { 0 } else { std::cmp::max(4, size_mem) }
}

pub fn template_type_aware_mem_size(
   e: &ExpressionType,
   udt: &UserDefinedTypeInfo,
   target: BaseTarget,
   templated_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
) -> Option<u64> {
   Some(match e {
      ExpressionType::Array(a_type, len) => {
         template_type_aware_mem_size(a_type, udt, target, templated_types)?.checked_mul(*len)?
      }
      ExpressionType::Union(union_id, generic_args) => {
         if generic_args.is_empty() {
            sizeof_type_mem(e, udt, target)
         } else {
            let mut our_mem_size = 0;
            let mut our_mem_alignment = 1;
            for field_t in udt.union_info[*union_id].field_types.values().map(|x| {
               map_generic_to_concrete_cow(
                  &x.e_type,
                  generic_args,
                  &templated_types[&UserDefinedTypeId::Union(*union_id)],
               )
            }) {
               our_mem_size = std::cmp::max(
                  our_mem_size,
                  template_type_aware_mem_size(&field_t, udt, target, templated_types)?,
               );
               our_mem_alignment = std::cmp::max(
                  our_mem_alignment,
                  template_type_aware_mem_alignment(&field_t, udt, target, templated_types),
               );
            }
            aligned_address(our_mem_size, our_mem_alignment)?
         }
      }
      ExpressionType::Struct(struct_id, generic_args) => {
         if generic_args.is_empty() {
            sizeof_type_mem(e, udt, target)
         } else {
            let iter = udt.struct_info[*struct_id].field_types.values().map(|x| {
               map_generic_to_concrete_cow(
                  &x.e_type,
                  generic_args,
                  &templated_types[&UserDefinedTypeId::Struct(*struct_id)],
               )
            });
            let zip_iter = iter.clone().skip(1).map(Some).chain(std::iter::once(None));
            let mut sum_mem: u64 = 0;
            let mut strictest_alignment = 1;
            for (field_t, next_field_t) in iter.zip(zip_iter) {
               let next_mem_alignment = next_field_t.map_or(1, |x| {
                  template_type_aware_mem_alignment(&x, udt, target, templated_types)
               });
               sum_mem = aligned_address(
                  sum_mem.checked_add(template_type_aware_mem_size(&field_t, udt, target, templated_types)?)?,
                  next_mem_alignment,
               )?;

               strictest_alignment = std::cmp::max(
                  strictest_alignment,
                  template_type_aware_mem_alignment(&field_t, udt, target, templated_types),
               );
            }
            aligned_address(sum_mem, strictest_alignment)?
         }
      }
      _ => sizeof_type_mem(e, udt, target),
   })
}

/// The size of a type as it's stored in memory
pub fn sizeof_type_mem(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: BaseTarget) -> u64 {
   match e {
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         sizeof_type_mem(&base_type.e_type, udt, target)
      }
      ExpressionType::Int(x) => u64::from(x.width.as_num_bytes(target)),
      ExpressionType::Float(x) => u64::from(x.width.as_num_bytes()),
      ExpressionType::Pointer(_) | ExpressionType::ProcedurePointer { .. } => u64::from(target.pointer_width()),
      ExpressionType::Bool => 1,
      ExpressionType::Unit | ExpressionType::Never | ExpressionType::ProcedureItem(_, _) => 0,
      ExpressionType::Struct(x, type_args) => {
         debug_assert!(type_args.is_empty());
         udt.struct_info.get(*x).unwrap().size.as_ref().unwrap().mem_size
      }
      ExpressionType::Array(a_type, len) => sizeof_type_mem(a_type, udt, target) * *len,
      ExpressionType::Union(x, type_args) => {
         debug_assert!(type_args.is_empty());
         udt.union_info.get(*x).unwrap().size.as_ref().unwrap().mem_size
      }
      ExpressionType::GenericParam(_)
      | ExpressionType::CompileError
      | ExpressionType::Unresolved { .. }
      | ExpressionType::Unknown(_) => unreachable!(),
   }
}
