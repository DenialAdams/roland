use std::collections::HashMap;

use byteorder::{LittleEndian, WriteBytesExt};
use indexmap::{IndexMap, IndexSet};
use std::io::Write;

use crate::interner::{Interner, StrId};
use crate::parse::{ExpressionPool, ProcImplSource, Program};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::sizeof_type_values;
use crate::type_data::{ExpressionType, FloatWidth, IntWidth, ValueType};

use super::wast_emitter::PrettyWasmWriter;
use super::GenerationContext;

const F64_B: u8 = 0x7c;
const F32_B: u8 = 0x7d;
const I64_B: u8 = 0x7e;
const I32_B: u8 = 0x7f;

pub fn u32_at(out: &mut [u8], pos: usize, mut amt: u32) {
   const U32_MAX_LEN: usize = 5;
   for i in 0..U32_MAX_LEN {
      let flag = if i == U32_MAX_LEN - 1 { 0 } else { 0x80 };
      out[pos + i] = (amt as u8) & 0x7f | flag;
      amt >>= 7;
   }
}

pub fn emit_name(out: &mut Vec<u8>, name: &str) {
   leb128::write::unsigned(out, name.len() as u64).unwrap();
   out.write_all(name.as_bytes()).unwrap();
}

// Returns the index of the (5 byte) placeholder, to be fixed up later
pub fn section_size_placeholder(out: &mut Vec<u8>) -> usize {
   let fixup_index = out.len();
   out.write_u8(0x00).unwrap();
   out.write_u8(0x00).unwrap();
   out.write_u8(0x00).unwrap();
   out.write_u8(0x00).unwrap();
   out.write_u8(0x00).unwrap();
   fixup_index
}

fn type_to_b(e: &ExpressionType, out: &mut Vec<u8>, ei: &IndexMap<StrId, EnumInfo>, si: &IndexMap<StrId, StructInfo>) {
   match e {
      ExpressionType::Value(x) => value_type_to_b(x, out, ei, si),
      ExpressionType::Pointer(_, _) => out.push(I32_B),
   }
}

fn value_type_to_b(e: &ValueType, out: &mut Vec<u8>, ei: &IndexMap<StrId, EnumInfo>, si: &IndexMap<StrId, StructInfo>) {
   match e {
      ValueType::Unresolved(_) => unreachable!(),
      ValueType::UnknownInt => unreachable!(),
      ValueType::UnknownFloat => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => out.push(I64_B),
         _ => out.push(I32_B),
      },
      ValueType::Float(x) => match x.width {
         FloatWidth::Eight => out.push(F64_B),
         FloatWidth::Four => out.push(F32_B),
      },
      ValueType::Bool => out.push(I32_B),
      ValueType::Unit => (),
      ValueType::CompileError => unreachable!(),
      ValueType::Enum(x) => {
         let num_variants = ei.get(x).unwrap().variants.len();
         if num_variants > u32::MAX as usize {
            out.push(I64_B);
         } else {
            out.push(I32_B);
         }
      }
      ValueType::Struct(x) => {
         let field_types = &si.get(x).unwrap().field_types;
         for e_type in field_types.values() {
            type_to_b(e_type, out, ei, si);
         }
      }
      ValueType::Array(a_type, len) => {
         for _ in 0..*len {
            type_to_b(a_type, out, ei, si);
         }
      }
   }
}

pub fn emit_wasm(
   program: &mut Program,
   interner: &mut Interner,
   expressions: &ExpressionPool,
   memory_base: u32,
   wasm4: bool,
) -> Vec<u8> {
   let mut generation_context = GenerationContext {
      out: PrettyWasmWriter {
         out: Vec::new(),
         depth: 0,
      },
      literal_offsets: HashMap::with_capacity(program.literals.len()),
      static_addresses: HashMap::with_capacity(program.static_info.len()),
      local_offsets_mem: HashMap::new(),
      needed_store_fns: IndexSet::new(),
      struct_info: &program.struct_info,
      struct_size_info: &program.struct_size_info,
      enum_info: &program.enum_info,
      sum_sizeof_locals_mem: 0,
      expressions,
   };

   // WASM Magic Number
   generation_context.out.out.write_all(b"\0asm").unwrap();

   // WASM binary version
   generation_context.out.out.write_u32::<LittleEndian>(0x01).unwrap();

   {
      // Type Section
      generation_context.out.out.write_u8(0x01).unwrap();

      // size of section
      let section_size = section_size_placeholder(&mut generation_context.out.out);

      // # of types
      let num_types = program.procedures.len() + program.external_procedures.len();
      leb128::write::unsigned(&mut generation_context.out.out, num_types as u64).unwrap();

      for procedure_def in program
         .external_procedures
         .iter()
         .map(|x| &x.definition)
         .chain(program.procedures.iter().map(|x| &x.definition))
      {
         // func type
         generation_context.out.out.write_u8(0x60).unwrap();

         // inputs
         let num_input_values: u32 = procedure_def
            .parameters
            .iter()
            .map(|x| sizeof_type_values(&x.p_type, generation_context.struct_size_info))
            .sum();
         leb128::write::unsigned(&mut generation_context.out.out, u64::from(num_input_values)).unwrap();
         for param in procedure_def.parameters.iter() {
            type_to_b(
               &param.p_type,
               &mut generation_context.out.out,
               generation_context.enum_info,
               generation_context.struct_info,
            );
         }

         // outputs
         let num_output_values = sizeof_type_values(&procedure_def.ret_type, generation_context.struct_size_info);
         leb128::write::unsigned(&mut generation_context.out.out, u64::from(num_output_values)).unwrap();
         type_to_b(
            &procedure_def.ret_type,
            &mut generation_context.out.out,
            generation_context.enum_info,
            generation_context.struct_info,
         );
      }

      // fixup the size
      let sizeof_section = generation_context.out.out.len() - (section_size + 5);
      u32_at(&mut generation_context.out.out, section_size, sizeof_section as u32);
   }

   {
      // Import Section
      generation_context.out.out.write_u8(0x02).unwrap();

      // size of section
      let section_size = section_size_placeholder(&mut generation_context.out.out);

      // # of imports
      let num_imports = program
         .external_procedures
         .iter()
         .filter(|x| std::mem::discriminant(&x.impl_source) == std::mem::discriminant(&ProcImplSource::External))
         .count() + usize::from(wasm4);
      leb128::write::unsigned(&mut generation_context.out.out, num_imports as u64).unwrap();

      for (i, procedure) in
         program.external_procedures.iter().enumerate().filter(|(_, x)| {
            std::mem::discriminant(&x.impl_source) == std::mem::discriminant(&ProcImplSource::External)
         })
      {
         // module name
         if wasm4 {
            emit_name(&mut generation_context.out.out, "env");
         } else {
            emit_name(&mut generation_context.out.out, "wasi_unstable");
         }
         // function name
         emit_name(
            &mut generation_context.out.out,
            interner.lookup(procedure.definition.name),
         );
         // comes from the type section
         generation_context.out.out.write_u8(0x0).unwrap();
         // index into the type section
         leb128::write::unsigned(&mut generation_context.out.out, i as u64).unwrap();
      }

      if wasm4 {
         todo!("Need to import wasm4 memory");
      }

      // fixup the size
      let sizeof_section = generation_context.out.out.len() - (section_size + 5);
      u32_at(&mut generation_context.out.out, section_size, sizeof_section as u32);
   }

   {
      // Memory Section
      generation_context.out.out.write_u8(0x05).unwrap();

      // size of section
      let section_size = section_size_placeholder(&mut generation_context.out.out);

      // # of memories
      leb128::write::unsigned(&mut generation_context.out.out, u64::from(!wasm4)).unwrap();

      if !wasm4 {
         // no upper bound
         generation_context.out.out.write_u8(0x00).unwrap();
         // minimum 1
         leb128::write::unsigned(&mut generation_context.out.out, 0x1).unwrap();
      }

      // fixup the size
      let sizeof_section = generation_context.out.out.len() - (section_size + 5);
      u32_at(&mut generation_context.out.out, section_size, sizeof_section as u32);
   }

   {
      // Global Section
      generation_context.out.out.write_u8(0x06).unwrap();

      // size of section
      let section_size = section_size_placeholder(&mut generation_context.out.out);

      // # of globals
      leb128::write::unsigned(&mut generation_context.out.out, 0x3).unwrap();

      {
         // stack pointer
         {
            generation_context.out.out.push(I32_B); // i32
            generation_context.out.out.write_u8(0x01).unwrap(); // mutable

            generation_context.out.out.write_u8(0x01).unwrap(); // i32.const
         }
   writeln!(
      generation_context.out.out,
      "(global $sp (mut i32) (i32.const {}))",
      offset
   )
   .unwrap();
         // base pointer
         {
            generation_context.out.out.push(I32_B); // i32
            generation_context.out.out.write_u8(0x01).unwrap(); // mutable

            generation_context.out.out.write_u8(0x01).unwrap(); // i32.const
         }
   writeln!(
      generation_context.out.out,
      "(global $bp (mut i32) (i32.const {}))",
      offset
   )
   .unwrap();
         // mem_address
         {
            generation_context.out.out.push(I32_B); // i32
            generation_context.out.out.write_u8(0x01).unwrap(); // mutable

            generation_context.out.out.write_u8(0x01).unwrap(); // i32.const
            leb128::write::signed(&mut generation_context.out.out, 0x0).unwrap(); // 0
         }
      }

      // fixup the size
      let sizeof_section = generation_context.out.out.len() - (section_size + 5);
      u32_at(&mut generation_context.out.out, section_size, sizeof_section as u32);
   }

   generation_context.out.out
}
