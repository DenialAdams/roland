use std::collections::HashMap;

use indexmap::IndexSet;

use crate::interner::StrId;
use crate::parse::{StructId, UnionId, UserDefinedTypeId, UserDefinedTypeInfo};
use crate::type_data::{ExpressionType, FloatWidth, IntWidth};
use crate::Target;

#[derive(Clone)]
pub struct StructSizeInfo {
   pub mem_size: u32,
   pub strictest_alignment: u32,
   pub field_offsets_mem: HashMap<StrId, u32>,
}

#[derive(Clone)]
pub struct UnionSizeInfo {
   pub mem_size: u32,
   pub mem_alignment: u32,
}

pub fn aligned_address(v: u32, a: u32) -> u32 {
   let rem = v % a;
   if rem == 0 {
      v
   } else {
      v + (a - rem)
   }
}

pub fn calculate_union_size_info(
   id: UnionId,
   udt: &mut UserDefinedTypeInfo,
   target: Target,
   templated_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
) {
   if udt.union_info.get(id).unwrap().size.is_some() {
      return;
   }

   if templated_types.contains_key(&UserDefinedTypeId::Union(id)) {
      return;
   }

   let ft = std::mem::take(&mut udt.union_info.get_mut(id).unwrap().field_types);
   for field_t in ft.values() {
      match field_t.e_type {
         ExpressionType::Struct(s, _) => calculate_struct_size_info(s, udt, target, templated_types),
         ExpressionType::Union(s) => calculate_union_size_info(s, udt, target, templated_types),
         _ => (),
      }
   }
   udt.union_info.get_mut(id).unwrap().field_types = ft;

   let mut our_mem_size = 0;
   let mut our_mem_alignment = 1;

   for field_t in udt.union_info.get(id).unwrap().field_types.values() {
      let field_t = &field_t.e_type;

      our_mem_size = std::cmp::max(our_mem_size, sizeof_type_mem(field_t, udt, target));
      our_mem_alignment = std::cmp::max(our_mem_alignment, mem_alignment(field_t, udt, target));
   }

   udt.union_info.get_mut(id).unwrap().size = Some(UnionSizeInfo {
      mem_size: aligned_address(our_mem_size, our_mem_alignment),
      mem_alignment: our_mem_alignment,
   });
}

pub fn calculate_struct_size_info(
   id: StructId,
   udt: &mut UserDefinedTypeInfo,
   target: Target,
   templated_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
) {
   if udt.struct_info.get(id).unwrap().size.is_some() {
      return;
   }

   if templated_types.contains_key(&UserDefinedTypeId::Struct(id)) {
      return;
   }

   let ft = std::mem::take(&mut udt.struct_info.get_mut(id).unwrap().field_types);
   for field_t in ft.values() {
      match field_t.e_type {
         ExpressionType::Struct(s, _) => calculate_struct_size_info(s, udt, target, templated_types),
         ExpressionType::Union(s) => calculate_union_size_info(s, udt, target, templated_types),
         _ => (),
      }
   }
   udt.struct_info.get_mut(id).unwrap().field_types = ft;

   let mut sum_mem = 0;
   let mut strictest_alignment = 1;
   let mut field_offsets_mem = HashMap::with_capacity(udt.struct_info.get(id).unwrap().field_types.len());
   for ((field_name, field_t), next_field_t) in udt
      .struct_info
      .get(id)
      .unwrap()
      .field_types
      .iter()
      .zip(udt.struct_info.get(id).unwrap().field_types.values().skip(1))
   {
      let field_t = &field_t.e_type;
      let next_field_t = &next_field_t.e_type;

      field_offsets_mem.insert(*field_name, sum_mem);

      let our_mem_size = sizeof_type_mem(field_t, udt, target);
      // We align our size with the alignment of the next field to account for potential padding
      let next_mem_alignment = mem_alignment(next_field_t, udt, target);

      sum_mem += aligned_address(our_mem_size, next_mem_alignment);

      strictest_alignment = std::cmp::max(strictest_alignment, mem_alignment(field_t, udt, target));
   }

   if let Some((last_field_name, last_field_t_node)) = udt.struct_info.get(id).unwrap().field_types.iter().last() {
      let last_field_t = &last_field_t_node.e_type;

      field_offsets_mem.insert(*last_field_name, sum_mem);

      sum_mem += sizeof_type_mem(last_field_t, udt, target);
      strictest_alignment = std::cmp::max(strictest_alignment, mem_alignment(last_field_t, udt, target));
   }

   udt.struct_info.get_mut(id).unwrap().size = Some(StructSizeInfo {
      mem_size: aligned_address(sum_mem, strictest_alignment),
      strictest_alignment,
      field_offsets_mem,
   });
}

pub fn mem_alignment(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: Target) -> u32 {
   match e {
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         mem_alignment(base_type, udt, target)
      }
      ExpressionType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         IntWidth::Pointer => u32::from(target.pointer_width()),
         IntWidth::Four => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      },
      ExpressionType::Float(x) => match x.width {
         FloatWidth::Eight => 8,
         FloatWidth::Four => 4,
      },
      ExpressionType::Pointer(_) | ExpressionType::ProcedurePointer { .. } => u32::from(target.pointer_width()),
      ExpressionType::Struct(x, generic_args) => {
         udt.struct_info
            .get(*x)
            .unwrap()
            .size
            .as_ref()
            .unwrap()
            .strictest_alignment
      }
      ExpressionType::Array(a_type, _len) => mem_alignment(a_type, udt, target),
      ExpressionType::Union(x) => udt.union_info.get(*x).unwrap().size.as_ref().unwrap().mem_alignment,
      ExpressionType::Bool | ExpressionType::Unit | ExpressionType::Never | ExpressionType::ProcedureItem(_, _) => 1,
      ExpressionType::Unresolved { .. }
      | ExpressionType::Unknown(_)
      | ExpressionType::CompileError
      | ExpressionType::GenericParam(_) => unreachable!(),
   }
}

/// The size of a type, in number of WASM values
pub fn sizeof_type_values(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: Target) -> u32 {
   if sizeof_type_mem(e, udt, target) == 0 {
      return 0;
   }

   match e {
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         sizeof_type_values(base_type, udt, target)
      }
      ExpressionType::Int(_)
      | ExpressionType::Float(_)
      | ExpressionType::Pointer(_)
      | ExpressionType::Bool
      | ExpressionType::Struct(_, _)
      | ExpressionType::Array(_, _)
      | ExpressionType::ProcedurePointer { .. }
      | ExpressionType::Union(_) => 1,
      ExpressionType::ProcedureItem(_, _) | ExpressionType::Unit | ExpressionType::Never => 0,
      ExpressionType::GenericParam(_)
      | ExpressionType::CompileError
      | ExpressionType::Unresolved { .. }
      | ExpressionType::Unknown(_) => unreachable!(),
   }
}

/// The size of a type, in bytes, as it's stored in local memory (minimum size 4 bytes)
pub fn sizeof_type_wasm(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: Target) -> u32 {
   let size_mem = sizeof_type_mem(e, udt, target);
   if size_mem == 0 {
      0
   } else {
      std::cmp::max(4, size_mem)
   }
}

/// The size of a type as it's stored in memory
pub fn sizeof_type_mem(e: &ExpressionType, udt: &UserDefinedTypeInfo, target: Target) -> u32 {
   match e {
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         sizeof_type_mem(base_type, udt, target)
      }
      ExpressionType::Int(x) => u32::from(x.width.as_num_bytes(target)),
      ExpressionType::Float(x) => u32::from(x.width.as_num_bytes()),
      ExpressionType::Pointer(_) | ExpressionType::ProcedurePointer { .. } => u32::from(target.pointer_width()),
      ExpressionType::Bool => 1,
      ExpressionType::Unit | ExpressionType::Never | ExpressionType::ProcedureItem(_, _) => 0,
      ExpressionType::Struct(x, generic_args) => udt.struct_info.get(*x).unwrap().size.as_ref().unwrap().mem_size,
      ExpressionType::Array(a_type, len) => sizeof_type_mem(a_type, udt, target) * (*len),
      ExpressionType::Union(x) => udt.union_info.get(*x).unwrap().size.as_ref().unwrap().mem_size,
      ExpressionType::GenericParam(_)
      | ExpressionType::CompileError
      | ExpressionType::Unresolved { .. }
      | ExpressionType::Unknown(_) => unreachable!(),
   }
}
