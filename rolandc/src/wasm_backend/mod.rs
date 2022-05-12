use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::interner::StrId;
use crate::parse::ExpressionPool;
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::SizeInfo;
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
