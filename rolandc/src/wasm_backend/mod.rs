use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::interner::{Interner, StrId};
use crate::parse::{ExpressionPool, Program};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::{aligned_address, mem_alignment, sizeof_type_mem, SizeInfo};
use crate::type_data::ExpressionType;

pub mod wasm_emitter;
pub mod wast_emitter;

use wast_emitter::PrettyWasmWriter;

const MINIMUM_STACK_FRAME_SIZE: u32 = 4;

struct GenerationContext<'a> {
   out: PrettyWasmWriter, // TODO: 86 this member
   literal_offsets: HashMap<StrId, (u32, u32)>,
   static_addresses: HashMap<StrId, u32>,
   local_offsets_mem: HashMap<StrId, u32>,
   struct_info: &'a IndexMap<StrId, StructInfo>,
   struct_size_info: &'a HashMap<StrId, SizeInfo>,
   enum_info: &'a IndexMap<StrId, EnumInfo>,
   needed_store_fns: IndexSet<ExpressionType>,
   sum_sizeof_locals_mem: u32,
   expressions: &'a ExpressionPool,
}

fn compare_alignment(alignment_1: u32, sizeof_1: u32, alignment_2: u32, sizeof_2: u32) -> std::cmp::Ordering {
   let rem_1 = sizeof_1 % alignment_1;
   let required_padding_1 = if rem_1 == 0 { 0 } else { alignment_1 - rem_1 };

   let rem_2 = sizeof_2 % alignment_2;
   let required_padding_2 = if rem_2 == 0 { 0 } else { alignment_2 - rem_2 };

   // The idea is to process the types with the strictest alignment first, to minimize the amount of padding
   // Some amount of padding between objects is still necessary because we have structs
   // In that case, we put the structs towards the end to maybe save a couple of bytes per frame
   // (example: a struct that would require 7 bytes of padding if the following element was a u64 would
   // only require 3 bytes if the following element is a u32)
   // ... I'm actually not sure this makes sense, maybe it's better to confirm this empirically
   alignment_2
      .cmp(&alignment_1)
      .then(required_padding_1.cmp(&required_padding_2))
}

fn compare_type_alignment(
   e_1: &ExpressionType,
   e_2: &ExpressionType,
   enum_info: &IndexMap<StrId, EnumInfo>,
   struct_size_info: &HashMap<StrId, SizeInfo>,
) -> std::cmp::Ordering {
   let alignment_1 = mem_alignment(e_1, enum_info, struct_size_info);
   let alignment_2 = mem_alignment(e_2, enum_info, struct_size_info);

   let sizeof_1 = sizeof_type_mem(e_1, enum_info, struct_size_info);
   let sizeof_2 = sizeof_type_mem(e_1, enum_info, struct_size_info);

   compare_alignment(alignment_1, sizeof_1, alignment_2, sizeof_2)
}

// Returns the starting address of the program stack
fn compute_prestack_data(
   memory_base: u32,
   program: &Program,
   interner: &Interner,
   generation_context: &mut GenerationContext,
) -> u32 {
   let mut offset: u32 = memory_base;

   // string literals
   for s in program.literals.iter() {
      let str_value = interner.lookup(*s);
      let s_len = str_value.len() as u32;
      generation_context.literal_offsets.insert(*s, (offset, s_len));
      offset += s_len;
   }

   // Beginning of the statics is affected by the alignment requirements
   {
      // Assumes
      let strictest_alignment = if let Some(v) = program.static_info.first() {
         mem_alignment(
            &v.1.static_type,
            generation_context.enum_info,
            generation_context.struct_size_info,
         )
      } else {
         1
      };

      offset = aligned_address(offset, strictest_alignment);
   }

   // Statics
   for (static_name, static_details) in program.static_info.iter() {
      generation_context.static_addresses.insert(*static_name, offset);

      offset += sizeof_type_mem(
         &static_details.static_type,
         generation_context.enum_info,
         generation_context.struct_size_info,
      );
   }

   // keep stack aligned
   aligned_address(offset, 8)
}
