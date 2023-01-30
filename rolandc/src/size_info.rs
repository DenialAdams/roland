use std::collections::HashMap;

use indexmap::IndexMap;

use crate::interner::StrId;
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::type_data::{ExpressionType, FloatWidth, IntWidth, ValueType};

#[derive(Clone)]
pub struct SizeInfo {
   values_size: u32,
   pub mem_size: u32,
   pub strictest_alignment: u32,
   pub field_offsets: HashMap<StrId, u32>,
   pub contains_never_type: bool,
}

pub fn aligned_address(v: u32, a: u32) -> u32 {
   let rem = v % a;
   if rem == 0 {
      v
   } else {
      v + (a - rem)
   }
}

pub fn calculate_struct_size_info(
   name: StrId,
   enum_info: &IndexMap<StrId, EnumInfo>,
   struct_info: &IndexMap<StrId, StructInfo>,
   struct_size_info: &mut HashMap<StrId, SizeInfo>,
) {
   let mut sum_mem = 0;
   let mut sum_values = 0;
   let mut strictest_alignment = 1;
   let mut field_offsets = HashMap::with_capacity(struct_info.get(&name).unwrap().field_types.len());
   let mut contains_never_type = false;
   for ((field_name, field_t), next_field_t) in struct_info
      .get(&name)
      .unwrap()
      .field_types
      .iter()
      .zip(struct_info.get(&name).unwrap().field_types.values().skip(1))
   {
      let field_t = &field_t.e_type;
      let next_field_t = &next_field_t.e_type;

      if let ExpressionType::Value(ValueType::Struct(s)) = field_t {
         if !struct_size_info.contains_key(s) {
            calculate_struct_size_info(*s, enum_info, struct_info, struct_size_info);
         }
         contains_never_type |= struct_size_info.get(s).unwrap().contains_never_type;
      }

      if let ExpressionType::Value(ValueType::Struct(s)) = next_field_t {
         if !struct_size_info.contains_key(s) {
            calculate_struct_size_info(*s, enum_info, struct_info, struct_size_info);
         }
      }

      field_offsets.insert(*field_name, sum_mem);

      let our_mem_size = sizeof_type_mem(field_t, enum_info, struct_size_info);
      // We align our size with the alignment of the next field to account for potential padding
      let next_mem_alignment = mem_alignment(next_field_t, enum_info, struct_size_info);

      // todo: Check this addition for overflow?
      sum_mem += aligned_address(our_mem_size, next_mem_alignment);
      sum_values += sizeof_type_values(field_t, enum_info, struct_size_info);

      strictest_alignment = std::cmp::max(strictest_alignment, mem_alignment(field_t, enum_info, struct_size_info));

      contains_never_type |= field_t.is_never();
   }

   if let Some((last_field_name, last_field_t_node)) = struct_info.get(&name).unwrap().field_types.iter().last() {
      let last_field_t = &last_field_t_node.e_type;

      if let ExpressionType::Value(ValueType::Struct(s)) = last_field_t {
         if !struct_size_info.contains_key(s) {
            calculate_struct_size_info(*s, enum_info, struct_info, struct_size_info);
         }
         contains_never_type |= struct_size_info.get(s).unwrap().contains_never_type;
      }

      field_offsets.insert(*last_field_name, sum_mem);

      sum_mem += sizeof_type_mem(last_field_t, enum_info, struct_size_info);
      sum_values += sizeof_type_values(last_field_t, enum_info, struct_size_info);
      strictest_alignment = std::cmp::max(
         strictest_alignment,
         mem_alignment(last_field_t, enum_info, struct_size_info),
      );
      contains_never_type |= last_field_t.is_never();
   }

   struct_size_info.insert(
      name,
      SizeInfo {
         mem_size: aligned_address(sum_mem, strictest_alignment),
         values_size: sum_values,
         strictest_alignment,
         field_offsets,
         contains_never_type,
      },
   );
}

pub fn mem_alignment(e: &ExpressionType, ei: &IndexMap<StrId, EnumInfo>, si: &HashMap<StrId, SizeInfo>) -> u32 {
   match e {
      ExpressionType::Value(x) => value_type_mem_alignment(x, ei, si),
      ExpressionType::Pointer(_, _) => 4, // @FixedPointerWidth
   }
}

pub fn value_type_mem_alignment(e: &ValueType, ei: &IndexMap<StrId, EnumInfo>, si: &HashMap<StrId, SizeInfo>) -> u32 {
   match e {
      ValueType::Unresolved(_) => unreachable!(),
      ValueType::UnknownInt(_) => unreachable!(),
      ValueType::UnknownFloat(_) => unreachable!(),
      ValueType::Enum(x) => {
         let base_type = &ei.get(x).unwrap().base_type;
         value_type_mem_alignment(base_type, ei, si)
      }
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         // @FixedPointerWidth
         IntWidth::Four | IntWidth::Pointer => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      },
      ValueType::Float(x) => match x.width {
         FloatWidth::Eight => 8,
         FloatWidth::Four => 4,
      },
      ValueType::Bool => 1,
      ValueType::Unit => 1,
      ValueType::Never => 1,
      ValueType::ProcedurePointer { .. } => 4, // @FixedPointerWidth
      ValueType::ProcedureItem(_, _) => 1,
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => si.get(x).unwrap().strictest_alignment,
      ValueType::Array(a_type, _len) => mem_alignment(a_type, ei, si),
   }
}

/// The size of a type, in number of WASM values
pub fn sizeof_type_values(e: &ExpressionType, ei: &IndexMap<StrId, EnumInfo>, si: &HashMap<StrId, SizeInfo>) -> u32 {
   match e {
      ExpressionType::Value(x) => sizeof_value_type_values(x, ei, si),
      ExpressionType::Pointer(_, _) => 1,
   }
}

fn sizeof_value_type_values(e: &ValueType, ei: &IndexMap<StrId, EnumInfo>, si: &HashMap<StrId, SizeInfo>) -> u32 {
   match e {
      ValueType::Unresolved(_) => unreachable!(),
      ValueType::UnknownInt(_) => unreachable!(),
      ValueType::UnknownFloat(_) => unreachable!(),
      ValueType::Enum(x) => {
         let base_type = &ei.get(x).unwrap().base_type;
         sizeof_value_type_values(base_type, ei, si)
      }
      ValueType::Int(_) => 1,
      ValueType::Float(_) => 1,
      ValueType::Bool => 1,
      ValueType::Unit => 0,
      ValueType::Never => 0,
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => si.get(x).unwrap().values_size,
      ValueType::Array(a_type, len) => sizeof_type_values(a_type, ei, si) * (*len),
      ValueType::ProcedurePointer { .. } => 1,
      ValueType::ProcedureItem(_, _) => 0,
   }
}

/// The size of a type, in bytes, as it's stored in local memory (minimum size 4 bytes)
pub fn sizeof_type_wasm(e: &ExpressionType, ei: &IndexMap<StrId, EnumInfo>, si: &HashMap<StrId, SizeInfo>) -> u32 {
   if sizeof_type_mem(e, ei, si) == 0 {
      0
   } else {
      std::cmp::max(4, sizeof_type_mem(e, ei, si))
   }
}

/// The size of a type as it's stored in memory
pub fn sizeof_type_mem(e: &ExpressionType, ei: &IndexMap<StrId, EnumInfo>, si: &HashMap<StrId, SizeInfo>) -> u32 {
   match e {
      ExpressionType::Value(x) => sizeof_value_type_mem(x, ei, si),
      ExpressionType::Pointer(_, _) => 4, // @FixedPointerWidth
   }
}

pub fn sizeof_value_type_mem(e: &ValueType, ei: &IndexMap<StrId, EnumInfo>, si: &HashMap<StrId, SizeInfo>) -> u32 {
   match e {
      ValueType::Unresolved(_) => unreachable!(),
      ValueType::UnknownInt(_) => unreachable!(),
      ValueType::UnknownFloat(_) => unreachable!(),
      ValueType::Enum(x) => {
         let base_type = &ei.get(x).unwrap().base_type;
         sizeof_value_type_mem(base_type, ei, si)
      }
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         IntWidth::Four | IntWidth::Pointer => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      },
      ValueType::Float(x) => match x.width {
         FloatWidth::Eight => 8,
         FloatWidth::Four => 4,
      },
      ValueType::Bool => 1,
      ValueType::Unit => 0,
      ValueType::Never => 0,
      ValueType::ProcedurePointer { .. } => 4, // @FixedPointerWidth
      ValueType::ProcedureItem(_, _) => 0,
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => si.get(x).unwrap().mem_size,
      ValueType::Array(a_type, len) => sizeof_type_mem(a_type, ei, si) * (*len),
   }
}
