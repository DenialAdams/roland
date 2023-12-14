use std::collections::HashMap;

use slotmap::SlotMap;

use crate::interner::StrId;
use crate::parse::{EnumId, StructId, UnionId, UserDefinedTypeInfo};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::type_data::{ExpressionType, FloatWidth, IntWidth};

#[derive(Clone)]
pub struct StructSizeInfo {
   values_size: u32,
   pub mem_size: u32,
   pub strictest_alignment: u32,
   pub field_offsets_mem: HashMap<StrId, u32>,
   pub field_offsets_values: HashMap<StrId, u32>,
   pub contains_union_type: bool,
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

pub fn calculate_union_size_info(id: UnionId, udt: &mut UserDefinedTypeInfo) {
   if udt.union_info.get(id).unwrap().size.is_some() {
      return;
   }

   let ft = std::mem::take(&mut udt.union_info.get_mut(id).unwrap().field_types);
   for field_t in ft.values() {
      match field_t.e_type {
         ExpressionType::Struct(s) => calculate_struct_size_info(s, udt),
         ExpressionType::Union(s) => calculate_union_size_info(s, udt),
         _ => (),
      }
   }
   udt.union_info.get_mut(id).unwrap().field_types = ft;

   let mut our_mem_size = 0;
   let mut our_mem_alignment = 1;

   for field_t in udt.union_info.get(id).unwrap().field_types.values() {
      let field_t = &field_t.e_type;

      our_mem_size = std::cmp::max(our_mem_size, sizeof_type_mem(field_t, udt));
      our_mem_alignment = std::cmp::max(our_mem_alignment, mem_alignment(field_t, udt));
   }

   udt.union_info.get_mut(id).unwrap().size = Some(UnionSizeInfo {
      mem_size: aligned_address(our_mem_size, our_mem_alignment),
      mem_alignment: our_mem_alignment,
   });
}

pub fn calculate_struct_size_info(id: StructId, udt: &mut UserDefinedTypeInfo) {
   if udt.struct_info.get(id).unwrap().size.is_some() {
      return;
   }

   let ft = std::mem::take(&mut udt.struct_info.get_mut(id).unwrap().field_types);
   for field_t in ft.values() {
      match field_t.e_type {
         ExpressionType::Struct(s) => calculate_struct_size_info(s, udt),
         ExpressionType::Union(s) => calculate_union_size_info(s, udt),
         _ => (),
      }
   }
   udt.struct_info.get_mut(id).unwrap().field_types = ft;

   let mut sum_mem = 0;
   let mut sum_values = 0;
   let mut strictest_alignment = 1;
   let mut field_offsets_mem = HashMap::with_capacity(udt.struct_info.get(id).unwrap().field_types.len());
   let mut field_offsets_values = HashMap::with_capacity(udt.struct_info.get(id).unwrap().field_types.len());
   let mut contains_union_type = false;
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
      field_offsets_values.insert(*field_name, sum_values);

      let our_mem_size = sizeof_type_mem(field_t, udt);
      // We align our size with the alignment of the next field to account for potential padding
      let next_mem_alignment = mem_alignment(next_field_t, udt);

      // todo: Check this addition for overflow?
      sum_mem += aligned_address(our_mem_size, next_mem_alignment);
      sum_values += sizeof_type_values(field_t, &udt.enum_info, &udt.struct_info);

      strictest_alignment = std::cmp::max(strictest_alignment, mem_alignment(field_t, udt));

      contains_union_type |= field_t.is_or_contains_union(udt);
   }

   if let Some((last_field_name, last_field_t_node)) = udt.struct_info.get(id).unwrap().field_types.iter().last() {
      let last_field_t = &last_field_t_node.e_type;

      field_offsets_mem.insert(*last_field_name, sum_mem);
      field_offsets_values.insert(*last_field_name, sum_values);

      sum_mem += sizeof_type_mem(last_field_t, udt);
      sum_values += sizeof_type_values(last_field_t, &udt.enum_info, &udt.struct_info);
      strictest_alignment = std::cmp::max(strictest_alignment, mem_alignment(last_field_t, udt));
      contains_union_type |= last_field_t.is_or_contains_union(udt);
   }

   udt.struct_info.get_mut(id).unwrap().size = Some(StructSizeInfo {
      mem_size: aligned_address(sum_mem, strictest_alignment),
      values_size: sum_values,
      strictest_alignment,
      field_offsets_mem,
      field_offsets_values,
      contains_union_type,
   });
}

pub fn mem_alignment(e: &ExpressionType, udt: &UserDefinedTypeInfo) -> u32 {
   match e {
      ExpressionType::Unresolved(_) => unreachable!(),
      ExpressionType::Unknown(_) => unreachable!(),
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         mem_alignment(base_type, udt)
      }
      ExpressionType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         // @FixedPointerWidth
         IntWidth::Four | IntWidth::Pointer => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      },
      ExpressionType::Float(x) => match x.width {
         FloatWidth::Eight => 8,
         FloatWidth::Four => 4,
      },
      ExpressionType::Pointer(_) => 4, // @FixedPointerWidth
      ExpressionType::Bool => 1,
      ExpressionType::Unit => 1,
      ExpressionType::Never => 1,
      ExpressionType::ProcedurePointer { .. } => 4, // @FixedPointerWidth
      ExpressionType::ProcedureItem(_, _) => 1,
      ExpressionType::Struct(x) => {
         udt.struct_info
            .get(*x)
            .unwrap()
            .size
            .as_ref()
            .unwrap()
            .strictest_alignment
      }
      ExpressionType::Array(a_type, _len) => mem_alignment(a_type, udt),
      ExpressionType::CompileError => unreachable!(),
      ExpressionType::GenericParam(_) => unreachable!(),
      ExpressionType::Union(x) => udt.union_info.get(*x).unwrap().size.as_ref().unwrap().mem_alignment,
   }
}

/// The size of a type, in number of WASM values
pub fn sizeof_type_values(
   e: &ExpressionType,
   ei: &SlotMap<EnumId, EnumInfo>,
   si: &SlotMap<StructId, StructInfo>,
) -> u32 {
   match e {
      ExpressionType::Unresolved(_) => unreachable!(),
      ExpressionType::Unknown(_) => unreachable!(),
      ExpressionType::Enum(x) => {
         let base_type = &ei.get(*x).unwrap().base_type;
         sizeof_type_values(base_type, ei, si)
      }
      ExpressionType::Int(_) => 1,
      ExpressionType::Float(_) => 1,
      ExpressionType::Pointer(_) => 1,
      ExpressionType::Bool => 1,
      ExpressionType::Unit => 0,
      ExpressionType::Never => 0,
      ExpressionType::Struct(x) => si.get(*x).unwrap().size.as_ref().unwrap().values_size,
      ExpressionType::Array(a_type, len) => sizeof_type_values(a_type, ei, si) * (*len),
      ExpressionType::ProcedurePointer { .. } => 1,
      ExpressionType::ProcedureItem(_, _) => 0,
      ExpressionType::GenericParam(_) => unreachable!(),
      ExpressionType::CompileError => unreachable!(),
      ExpressionType::Union(_) => 1,
   }
}

/// The size of a type, in bytes, as it's stored in local memory (minimum size 4 bytes)
pub fn sizeof_type_wasm(e: &ExpressionType, udt: &UserDefinedTypeInfo) -> u32 {
   let size_mem = sizeof_type_mem(e, udt);
   if size_mem == 0 {
      0
   } else {
      std::cmp::max(4, size_mem)
   }
}

/// The size of a type as it's stored in memory
pub fn sizeof_type_mem(e: &ExpressionType, udt: &UserDefinedTypeInfo) -> u32 {
   match e {
      ExpressionType::Unresolved(_) => unreachable!(),
      ExpressionType::Unknown(_) => unreachable!(),
      ExpressionType::Enum(x) => {
         let base_type = &udt.enum_info.get(*x).unwrap().base_type;
         sizeof_type_mem(base_type, udt)
      }
      ExpressionType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         IntWidth::Four | IntWidth::Pointer => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      },
      ExpressionType::Float(x) => match x.width {
         FloatWidth::Eight => 8,
         FloatWidth::Four => 4,
      },
      ExpressionType::Pointer(_) => 4, // @FixedPointerWidth
      ExpressionType::Bool => 1,
      ExpressionType::Unit => 0,
      ExpressionType::Never => 0,
      ExpressionType::ProcedurePointer { .. } => 4, // @FixedPointerWidth
      ExpressionType::ProcedureItem(_, _) => 0,
      ExpressionType::Struct(x) => udt.struct_info.get(*x).unwrap().size.as_ref().unwrap().mem_size,
      ExpressionType::Array(a_type, len) => sizeof_type_mem(a_type, udt) * (*len),
      ExpressionType::GenericParam(_) => unreachable!(),
      ExpressionType::CompileError => unreachable!(),
      ExpressionType::Union(x) => udt.union_info.get(*x).unwrap().size.as_ref().unwrap().mem_size,
   }
}
