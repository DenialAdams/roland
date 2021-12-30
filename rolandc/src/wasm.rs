use crate::interner::{Interner, StrId};
use crate::parse::{
   BinOp, Expression, ExpressionIndex, ExpressionPool, ParameterNode, Program, Statement, StatementNode, UnOp,
};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::{mem_alignment, sizeof_type_mem, sizeof_type_values, sizeof_type_wasm, SizeInfo};
use crate::type_data::{ExpressionType, FloatWidth, IntType, IntWidth, ValueType, USIZE_TYPE};
use crate::typed_index_vec::Handle;
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};
use std::io::Write;

const MINIMUM_STACK_FRAME_SIZE: u32 = 4;

struct GenerationContext<'a> {
   out: PrettyWasmWriter,
   literal_offsets: HashMap<StrId, (u32, u32)>,
   static_addresses: HashMap<StrId, u32>,
   local_offsets_mem: HashMap<StrId, u32>,
   struct_info: &'a IndexMap<StrId, StructInfo>,
   struct_size_info: &'a HashMap<StrId, SizeInfo>,
   enum_info: &'a IndexMap<StrId, EnumInfo>,
   needed_store_fns: IndexSet<ExpressionType>,
   sum_sizeof_locals_mem: u32,
   loop_depth: u64,
   loop_counter: u64,
   expressions: &'a ExpressionPool,
}

struct PrettyWasmWriter {
   out: Vec<u8>,
   depth: usize,
}

impl<'a> PrettyWasmWriter {
   fn close(&mut self) {
      self.depth -= 1;
      self.emit_spaces();
      writeln!(self.out, ")").unwrap();
   }

   fn emit_spaces(&mut self) {
      let num_spaces = self.depth * 2;
      self.out.reserve(num_spaces);
      for _ in 0..num_spaces {
         self.out.push(b' ');
      }
   }

   fn emit_function_start_named_params(
      &mut self,
      name: StrId,
      params: &[ParameterNode],
      result_type: &ExpressionType,
      ei: &IndexMap<StrId, EnumInfo>,
      si: &IndexMap<StrId, StructInfo>,
      interner: &Interner,
   ) {
      self.emit_spaces();
      write!(self.out, "(func ${}", interner.lookup(name)).unwrap();
      for param in params.iter() {
         self.out.push(b' ');
         write_type_as_params(&param.p_type, &mut self.out, ei, si);
      }
      self.out.push(b' ');
      write_type_as_result(result_type, &mut self.out, ei, si);
      self.out.push(b'\n');
      self.depth += 1;
   }

   fn emit_store_function_start(
      &mut self,
      index: usize,
      param: &ExpressionType,
      ei: &IndexMap<StrId, EnumInfo>,
      si: &IndexMap<StrId, StructInfo>,
   ) {
      self.emit_spaces();
      write!(self.out, "(func $::store::{} (param i32) ", index).unwrap();
      write_type_as_params(param, &mut self.out, ei, si);
      self.out.push(b'\n');
      self.depth += 1;
   }

   fn emit_block_start(&mut self, label_val: u64) {
      self.emit_spaces();
      writeln!(self.out, "block $b_{}", label_val).unwrap();
      self.depth += 1;
   }

   fn emit_loop_start(&mut self, label_val: u64) {
      self.emit_spaces();
      writeln!(self.out, "loop $l_{}", label_val).unwrap();
      self.depth += 1;
   }

   fn emit_end(&mut self) {
      self.depth -= 1;
      self.emit_spaces();
      writeln!(self.out, "end").unwrap();
   }

   fn emit_if_start(
      &mut self,
      result_type: &ExpressionType,
      ei: &IndexMap<StrId, EnumInfo>,
      si: &IndexMap<StrId, StructInfo>,
   ) {
      self.emit_spaces();
      write!(self.out, "(if ").unwrap();
      write_type_as_result(result_type, &mut self.out, ei, si);
      self.out.push(b'\n');
      self.depth += 1;
   }

   fn emit_then_start(&mut self) {
      self.emit_spaces();
      writeln!(self.out, "(then ").unwrap();
      self.depth += 1;
   }

   fn emit_else_start(&mut self) {
      self.emit_spaces();
      writeln!(self.out, "(else ").unwrap();
      self.depth += 1;
   }

   fn emit_constant_sexp(&mut self, sexp: &str) {
      self.emit_spaces();
      writeln!(self.out, "{}", sexp).unwrap();
   }

   fn emit_constant_instruction(&mut self, instr: &str) {
      self.emit_spaces();
      writeln!(self.out, "{}", instr).unwrap();
   }

   fn emit_data(&mut self, mem_index: u32, offset: u32, literal: &str) {
      self.emit_spaces();
      write!(&mut self.out, "(data {} (i32.const {}) \"", mem_index, offset).unwrap();
      for byte in literal.as_bytes() {
         match byte {
            b'\\' => write!(self.out, "\\").unwrap(),
            b'\n' => write!(self.out, "\\n").unwrap(),
            b'\r' => write!(self.out, "\\r").unwrap(),
            b'\t' => write!(self.out, "\\t").unwrap(),
            b'\0' => write!(self.out, "\\u{{0}}").unwrap(),
            b'"' => write!(self.out, "\\\"").unwrap(),
            _ => self.out.push(*byte),
         }
      }
      writeln!(self.out, "\")").unwrap();
   }

   fn emit_get_local(&mut self, local_index: u32) {
      self.emit_spaces();
      writeln!(&mut self.out, "local.get {}", local_index).unwrap();
   }

   fn emit_set_global(&mut self, global_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "global.set ${}", global_name).unwrap();
   }

   fn emit_get_global(&mut self, global_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "global.get ${}", global_name).unwrap();
   }

   fn emit_call(&mut self, func_name: StrId, interner: &Interner) {
      self.emit_spaces();
      writeln!(&mut self.out, "call ${}", interner.lookup(func_name)).unwrap();
   }

   fn emit_const_i32(&mut self, value: u32) {
      self.emit_spaces();
      writeln!(&mut self.out, "i32.const {}", value).unwrap();
   }

   fn emit_const_add_i32(&mut self, value: u32) {
      if value > 0 {
         self.emit_const_i32(value);
         self.emit_spaces();
         writeln!(self.out, "i32.add").unwrap();
      }
   }

   fn emit_const_mul_i32(&mut self, value: u32) {
      if value != 1 {
         self.emit_const_i32(value);
         self.emit_spaces();
         writeln!(self.out, "i32.mul").unwrap();
      }
   }
}

fn write_type_as_result(
   e: &ExpressionType,
   out: &mut Vec<u8>,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) {
   match e {
      ExpressionType::Value(x) => write_value_type_as_result(x, out, ei, si),
      ExpressionType::Pointer(_, _) => write!(out, "(result i32)").unwrap(),
   }
}

fn write_value_type_as_result(
   e: &ValueType,
   out: &mut Vec<u8>,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) {
   match e {
      ValueType::Unresolved(_) => unreachable!(),
      ValueType::UnknownInt => unreachable!(),
      ValueType::UnknownFloat => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => write!(out, "(result i64)").unwrap(),
         _ => write!(out, "(result i32)").unwrap(),
      },
      ValueType::Enum(_) => {
         write!(out, "(result ").unwrap();
         value_type_to_s(e, out, ei, si);
         write!(out, ")").unwrap();
      }
      ValueType::Float(x) => match x.width {
         FloatWidth::Eight => write!(out, "(result f64)").unwrap(),
         FloatWidth::Four => write!(out, "(result i32)").unwrap(),
      },
      ValueType::Bool => write!(out, "(result i32)").unwrap(),
      ValueType::Unit => (),
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => {
         let field_types = &si.get(x).unwrap().field_types;
         for e_type in field_types.values() {
            write_type_as_result(e_type, out, ei, si);
            out.push(b' ');
         }
         if !field_types.is_empty() {
            let _ = out.pop();
         }
      }
      ValueType::Array(a_type, len) => {
         for _ in 0..*len {
            write_type_as_result(a_type, out, ei, si);
            out.push(b' ');
         }
         if *len > 0 {
            let _ = out.pop();
         }
      }
   }
}

fn write_type_as_params(
   e: &ExpressionType,
   out: &mut Vec<u8>,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) {
   match e {
      ExpressionType::Value(x) => write_value_type_as_params(x, out, ei, si),
      ExpressionType::Pointer(_, _) => write!(out, "(param i32)").unwrap(),
   }
}

fn write_value_type_as_params(
   e: &ValueType,
   out: &mut Vec<u8>,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) {
   match e {
      ValueType::Unresolved(_) => unreachable!(),
      ValueType::UnknownInt => unreachable!(),
      ValueType::UnknownFloat => unreachable!(),
      ValueType::Enum(_) => {
         write!(out, "(param ").unwrap();
         value_type_to_s(e, out, ei, si);
         write!(out, ")").unwrap();
      }
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => write!(out, "(param i64)").unwrap(),
         _ => write!(out, "(param i32)").unwrap(),
      },
      ValueType::Float(x) => match x.width {
         FloatWidth::Eight => write!(out, "(param f64)").unwrap(),
         FloatWidth::Four => write!(out, "(param i32)").unwrap(),
      },
      ValueType::Bool => write!(out, "(param i32)").unwrap(),
      ValueType::Unit => (),
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => {
         let field_types = &si.get(x).unwrap().field_types;
         for e_type in field_types.values() {
            write_type_as_params(e_type, out, ei, si);
            out.push(b' ');
         }
         if !field_types.is_empty() {
            let _ = out.pop();
         }
      }
      ValueType::Array(a_type, len) => {
         for _ in 0..*len {
            write_type_as_params(a_type, out, ei, si);
            out.push(b' ');
         }
         if *len > 0 {
            let _ = out.pop();
         }
      }
   }
}

fn type_to_s(e: &ExpressionType, out: &mut Vec<u8>, ei: &IndexMap<StrId, EnumInfo>, si: &IndexMap<StrId, StructInfo>) {
   match e {
      ExpressionType::Value(x) => value_type_to_s(x, out, ei, si),
      ExpressionType::Pointer(_, _) => write!(out, "i32").unwrap(),
   }
}

fn value_type_to_s(e: &ValueType, out: &mut Vec<u8>, ei: &IndexMap<StrId, EnumInfo>, si: &IndexMap<StrId, StructInfo>) {
   match e {
      ValueType::Unresolved(_) => unreachable!(),
      ValueType::UnknownInt => unreachable!(),
      ValueType::UnknownFloat => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => write!(out, "i64").unwrap(),
         _ => write!(out, "i32").unwrap(),
      },
      ValueType::Float(x) => match x.width {
         FloatWidth::Eight => write!(out, "f64").unwrap(),
         FloatWidth::Four => write!(out, "i32").unwrap(),
      },
      ValueType::Bool => write!(out, "i32").unwrap(),
      ValueType::Unit => unreachable!(),
      ValueType::CompileError => unreachable!(),
      ValueType::Enum(x) => {
         let num_variants = ei.get(x).unwrap().variants.len();
         if num_variants > u32::MAX as usize {
            write!(out, "i64").unwrap();
         } else {
            write!(out, "i32").unwrap();
         }
      }
      ValueType::Struct(x) => {
         let field_types = &si.get(x).unwrap().field_types;
         for e_type in field_types.values() {
            type_to_s(e_type, out, ei, si);
            out.push(b' ');
         }
         if !field_types.is_empty() {
            let _ = out.pop();
         }
      }
      ValueType::Array(a_type, len) => {
         for _ in 0..*len {
            type_to_s(a_type, out, ei, si);
            out.push(b' ');
         }
         if *len > 0 {
            let _ = out.pop();
         }
      }
   }
}

fn int_to_wasm_runtime_and_suffix(x: &IntType) -> (&'static str, &'static str) {
   let wasm_type = match x.width {
      IntWidth::Eight => "i64",
      _ => "i32",
   };
   let suffix = if x.signed { "_s" } else { "_u" };
   (wasm_type, suffix)
}

fn aligned_address(v: u32, a: u32) -> u32 {
   let rem = v % a;
   if rem != 0 {
      v + (a - rem)
   } else {
      v
   }
}

fn dynamic_move_locals_of_type_to_dest(
   memory_lookup: &str,
   offset: &mut u32,
   local_index: &mut u32,
   field: &ExpressionType,
   generation_context: &mut GenerationContext,
) {
   match field {
      ExpressionType::Value(ValueType::Unit) => (),
      ExpressionType::Value(ValueType::Struct(x)) => {
         for sub_field in generation_context.struct_info.get(x).unwrap().field_types.values() {
            dynamic_move_locals_of_type_to_dest(memory_lookup, offset, local_index, sub_field, generation_context);
         }
      }
      ExpressionType::Value(ValueType::Array(inner_type, a_len)) => {
         for _ in 0..*a_len {
            dynamic_move_locals_of_type_to_dest(memory_lookup, offset, local_index, inner_type, generation_context);
         }
      }
      _ => {
         generation_context.out.emit_constant_instruction(memory_lookup);
         generation_context.out.emit_const_add_i32(*offset);
         generation_context.out.emit_get_local(*local_index);
         simple_store(field, generation_context);
         *offset += sizeof_type_mem(field, generation_context.enum_info, generation_context.struct_size_info);
         *local_index += 1;
      }
   }
}

// MEMORY LAYOUT
// 0-l literals
// l-s statics
// s+ program stack (local variables and parameters are pushed here during runtime)
pub fn emit_wasm(
   struct_size_info: &HashMap<StrId, SizeInfo>,
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
      // todo: just reuse the same map?
      literal_offsets: HashMap::with_capacity(program.literals.len()),
      static_addresses: HashMap::with_capacity(program.static_info.len()),
      local_offsets_mem: HashMap::new(),
      needed_store_fns: IndexSet::new(),
      struct_info: &program.struct_info,
      struct_size_info,
      enum_info: &program.enum_info,
      sum_sizeof_locals_mem: 0,
      loop_counter: 0,
      loop_depth: 0,
      expressions,
   };

   for external_procedure in program.external_procedures.iter() {
      // These are roland builtins and not WASI; a way to distinguish this at the roland level might be good
      if external_procedure.definition.name == interner.intern("wasm_memory_grow")
         || external_procedure.definition.name == interner.intern("wasm_memory_size")
      {
         continue;
      }

      if wasm4 {
         writeln!(
            generation_context.out.out,
            "(import \"env\" \"{}\" ",
            interner.lookup(external_procedure.definition.name),
         )
         .unwrap();
      } else {
         writeln!(
            generation_context.out.out,
            "(import \"wasi_unstable\" \"{}\" ",
            interner.lookup(external_procedure.definition.name),
         )
         .unwrap();
      }

      generation_context.out.emit_function_start_named_params(
         external_procedure.definition.name,
         &external_procedure.definition.parameters,
         &external_procedure.definition.ret_type,
         &program.enum_info,
         &program.struct_info,
         interner,
      );
      generation_context.out.close();

      // close the import
      generation_context.out.out.push(b')');
      generation_context.out.out.push(b'\n');
   }

   if wasm4 {
      generation_context
         .out
         .emit_constant_sexp("(import \"env\" \"memory\" (memory 1 1))");
      generation_context
         .out
         .emit_constant_sexp("(export \"update\" (func $update))");
      generation_context
         .out
         .emit_constant_sexp("(export \"start\" (func $start))");
   } else {
      generation_context.out.emit_constant_sexp("(memory 1)");
      generation_context
         .out
         .emit_constant_sexp("(export \"memory\" (memory 0))");
      generation_context
         .out
         .emit_constant_sexp("(export \"_start\" (func $main))");
   }

   // Data section

   let mut offset: u32 = memory_base;

   for s in program.literals.iter() {
      let str_value = interner.lookup(*s);
      generation_context.out.emit_data(0, offset, str_value);
      //TODO: and here truncation
      let s_len = str_value.len() as u32;
      generation_context.literal_offsets.insert(*s, (offset, s_len));
      // TODO: check for overflow here
      offset += s_len;
   }

   // Handle alignment of statics
   {
      program.static_info.sort_by(|_k_1, v_1, _k_2, v_2| {
         compare_type_alignment(&v_1.static_type, &v_2.static_type, &generation_context)
      });

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
   for (static_name, static_details) in program.static_info.iter() {
      generation_context.static_addresses.insert(*static_name, offset);

      offset += sizeof_type_mem(
         &static_details.static_type,
         generation_context.enum_info,
         generation_context.struct_size_info,
      );
   }

   for p_static in program.statics.iter().filter(|x| x.value.is_some()) {
      let static_address = generation_context
         .static_addresses
         .get(&p_static.name.identifier)
         .copied()
         .unwrap();

      generation_context.out.emit_spaces();
      write!(
         &mut generation_context.out.out,
         "(data 0 (i32.const {}) \"",
         static_address
      )
      .unwrap();
      emit_literal_bytes(p_static.value.unwrap(), &mut generation_context, interner);
      writeln!(generation_context.out.out, "\")").unwrap();
   }

   // keep stack aligned
   offset = aligned_address(offset, 8);

   generation_context.out.emit_spaces();
   writeln!(
      generation_context.out.out,
      "(global $sp (mut i32) (i32.const {}))",
      offset
   )
   .unwrap();
   generation_context.out.emit_spaces();
   writeln!(
      generation_context.out.out,
      "(global $bp (mut i32) (i32.const {}))",
      offset
   )
   .unwrap();
   generation_context.out.emit_spaces();
   writeln!(
      generation_context.out.out,
      "(global $mem_address (mut i32) (i32.const 0))"
   )
   .unwrap();

   // builtin wasm memory size
   generation_context.out.emit_function_start_named_params(
      interner.intern("wasm_memory_size"),
      &[],
      &ExpressionType::Value(USIZE_TYPE),
      &program.enum_info,
      &program.struct_info,
      interner,
   );
   generation_context.out.emit_constant_instruction("memory.size");
   generation_context.out.close();

   // builtin wasm memory grow
   let new_pages_param = ParameterNode {
      name: interner.intern("new_pages"),
      p_type: ExpressionType::Value(USIZE_TYPE),
      named: false,
   };
   generation_context.out.emit_function_start_named_params(
      interner.intern("wasm_memory_grow"),
      &[new_pages_param],
      &ExpressionType::Value(USIZE_TYPE),
      &program.enum_info,
      &program.struct_info,
      interner,
   );
   generation_context.out.emit_get_local(0);
   generation_context.out.emit_constant_instruction("memory.grow");
   generation_context.out.close();

   for s in program.struct_info.iter() {
      let mut offset_begin = 0;
      for field in s.1.field_types.iter() {
         // todo: we can avoid this allocation by re-examaning the emit_function_start abstraction (we could push directly into the underlying buffer?)
         let full_name = interner.intern(&format!(
            "::struct::{}::{}",
            interner.lookup(*s.0),
            interner.lookup(*field.0)
         ));
         let param = ParameterNode {
            name: interner.intern(""),
            p_type: ExpressionType::Value(ValueType::Struct(*s.0)),
            named: false,
         };
         generation_context.out.emit_function_start_named_params(
            full_name,
            &[param],
            field.1,
            &program.enum_info,
            &program.struct_info,
            interner,
         );

         let offset_end = offset_begin + sizeof_type_values(field.1, generation_context.struct_size_info);

         for i in offset_begin..offset_end {
            generation_context.out.emit_get_local(i);
         }

         generation_context.out.close();

         offset_begin = offset_end;
      }
   }

   for procedure in program.procedures.iter_mut() {
      // This is very hacky, we're creating a bunch of strings for things that don't need to be strings!
      // We shouldn't do this, and instead make the following logic applicable to both StrId/ExpressionId
      // But this is my lazy approach for now, and I at least moved the logic right next to where it should go
      for expr in procedure.virtual_locals.iter().copied() {
         procedure
            .locals
            .entry(interner.intern(&format!("::{}", expr.index())))
            .or_insert_with(HashSet::new)
            .insert(generation_context.expressions[expr].exp_type.clone().unwrap());
      }

      generation_context.local_offsets_mem.clear();

      // 0-4 == value of previous frame base pointer
      generation_context.sum_sizeof_locals_mem = MINIMUM_STACK_FRAME_SIZE;

      let mut mem_info: IndexMap<StrId, (u32, u32)> = procedure
         .locals
         .iter()
         .map(|x| {
            let strictest_alignment =
               x.1.iter()
                  .map(|y| mem_alignment(y, generation_context.enum_info, generation_context.struct_size_info))
                  .max()
                  .unwrap();
            let biggest_size =
               x.1.iter()
                  .map(|y| sizeof_type_mem(y, generation_context.enum_info, generation_context.struct_size_info))
                  .max()
                  .unwrap();
            (*x.0, (strictest_alignment, biggest_size))
         })
         .collect();

      // Handle alignment within frame
      {
         mem_info.sort_by(|_k_1, v_1, _k_2, v_2| compare_alignment(v_1.0, v_1.1, v_2.0, v_2.1));

         let strictest_alignment = if let Some(v) = mem_info.first() { v.1 .0 } else { 1 };

         generation_context.sum_sizeof_locals_mem =
            aligned_address(generation_context.sum_sizeof_locals_mem, strictest_alignment);
      }

      for local in mem_info.iter() {
         // last element could have been a struct, and so we need to pad
         generation_context.sum_sizeof_locals_mem =
            aligned_address(generation_context.sum_sizeof_locals_mem, local.1 .0);
         generation_context
            .local_offsets_mem
            .insert(*local.0, generation_context.sum_sizeof_locals_mem);

         // TODO: should we check for overflow on this value?
         generation_context.sum_sizeof_locals_mem += local.1 .1;
      }

      generation_context.out.emit_function_start_named_params(
         procedure.definition.name,
         &procedure.definition.parameters,
         &procedure.definition.ret_type,
         &program.enum_info,
         &program.struct_info,
         interner,
      );

      adjust_stack_function_entry(&mut generation_context);

      // Copy parameters to stack memory so we can take pointers
      let mut values_index = 0;
      for param in &procedure.definition.parameters {
         match sizeof_type_values(&param.p_type, generation_context.struct_size_info).cmp(&1) {
            std::cmp::Ordering::Less => (),
            std::cmp::Ordering::Equal => {
               get_stack_address_of_local(param.name, &mut generation_context);
               generation_context.out.emit_get_local(values_index);
               simple_store(&param.p_type, &mut generation_context);
               values_index += 1;
            }
            std::cmp::Ordering::Greater => {
               get_stack_address_of_local(param.name, &mut generation_context);
               generation_context.out.emit_set_global("mem_address");
               dynamic_move_locals_of_type_to_dest(
                  "global.get $mem_address",
                  &mut 0,
                  &mut values_index,
                  &param.p_type,
                  &mut generation_context,
               );
            }
         }
      }

      for statement in &procedure.block.statements {
         emit_statement(statement, &mut generation_context, interner);
      }

      if let Some(Statement::Return(_)) = procedure.block.statements.last().map(|x| &x.statement) {
         // No need to adjust stack; it was done in the return statement
      } else {
         adjust_stack_function_exit(&mut generation_context);
      }

      generation_context.out.close();
   }

   let mut needed_store_fns = IndexSet::new();
   std::mem::swap(&mut needed_store_fns, &mut generation_context.needed_store_fns);
   for (i, e_type) in needed_store_fns.iter().enumerate() {
      generation_context.out.emit_store_function_start(
         i,
         e_type,
         generation_context.enum_info,
         generation_context.struct_info,
      );
      dynamic_move_locals_of_type_to_dest("local.get 0", &mut 0, &mut 1, e_type, &mut generation_context);
      generation_context.out.close();
   }

   generation_context.out.out
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
   generation_context: &GenerationContext,
) -> std::cmp::Ordering {
   let alignment_1 = mem_alignment(e_1, generation_context.enum_info, generation_context.struct_size_info);
   let alignment_2 = mem_alignment(e_2, generation_context.enum_info, generation_context.struct_size_info);

   let sizeof_1 = sizeof_type_mem(e_1, generation_context.enum_info, generation_context.struct_size_info);
   let sizeof_2 = sizeof_type_mem(e_1, generation_context.enum_info, generation_context.struct_size_info);

   compare_alignment(alignment_1, sizeof_1, alignment_2, sizeof_2)
}

fn emit_statement(statement: &StatementNode, generation_context: &mut GenerationContext, interner: &mut Interner) {
   match &statement.statement {
      Statement::Assignment(len, en) => {
         do_emit(*len, generation_context, interner);
         do_emit_and_load_lval(*en, generation_context, interner);
         let val_type = generation_context.expressions[*en].exp_type.as_ref().unwrap();
         store(val_type, generation_context, interner);
      }
      Statement::VariableDeclaration(id, en, _) => {
         get_stack_address_of_local(id.identifier, generation_context);
         do_emit_and_load_lval(*en, generation_context, interner);
         let val_type = generation_context.expressions[*en].exp_type.as_ref().unwrap();
         store(val_type, generation_context, interner);
      }
      Statement::Block(bn) => {
         for statement in &bn.statements {
            emit_statement(statement, generation_context, interner);
         }
      }
      Statement::For(var, start, end, bn, inclusive) => {
         let start_expr = &generation_context.expressions[*start];

         let (wasm_type, suffix) = match start_expr.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => int_to_wasm_runtime_and_suffix(x),
            _ => unreachable!(),
         };

         if *inclusive {
            todo!();
         }

         let end_var_id = interner.intern(&format!("::{}", end.index()));

         // Set start var
         {
            get_stack_address_of_local(var.identifier, generation_context);
            do_emit_and_load_lval(*start, generation_context, interner);
            store(start_expr.exp_type.as_ref().unwrap(), generation_context, interner);
         }
         // Set end var
         {
            get_stack_address_of_local(end_var_id, generation_context);
            do_emit_and_load_lval(*end, generation_context, interner);
            store(start_expr.exp_type.as_ref().unwrap(), generation_context, interner);
         }
         generation_context.loop_depth += 1;
         generation_context.out.emit_block_start(generation_context.loop_counter);
         generation_context.out.emit_loop_start(generation_context.loop_counter);
         generation_context.loop_counter += 1;
         // Check and break if needed
         {
            get_stack_address_of_local(var.identifier, generation_context);
            load(start_expr.exp_type.as_ref().unwrap(), generation_context);
            get_stack_address_of_local(end_var_id, generation_context);
            load(start_expr.exp_type.as_ref().unwrap(), generation_context);
            generation_context.out.emit_spaces();
            writeln!(generation_context.out.out, "{}.ge{}", wasm_type, suffix).unwrap();

            generation_context.out.emit_if_start(
               &ExpressionType::Value(ValueType::Unit),
               generation_context.enum_info,
               generation_context.struct_info,
            );
            // then
            generation_context.out.emit_then_start();
            generation_context.out.emit_spaces();
            writeln!(
               generation_context.out.out,
               "br $b_{}",
               generation_context.loop_counter - generation_context.loop_depth
            )
            .unwrap();
            generation_context.out.close();
            // finish if
            generation_context.out.close();
         }
         for statement in &bn.statements {
            emit_statement(statement, generation_context, interner);
         }
         // Increment
         {
            get_stack_address_of_local(var.identifier, generation_context);
            get_stack_address_of_local(var.identifier, generation_context);
            load(start_expr.exp_type.as_ref().unwrap(), generation_context);
            generation_context.out.emit_spaces();
            writeln!(generation_context.out.out, "{}.const 1", wasm_type).unwrap();
            generation_context.out.emit_spaces();
            writeln!(generation_context.out.out, "{}.add", wasm_type).unwrap();
            store(start_expr.exp_type.as_ref().unwrap(), generation_context, interner);
         }
         generation_context.out.emit_spaces();
         writeln!(
            generation_context.out.out,
            "br $l_{}",
            generation_context.loop_counter - generation_context.loop_depth
         )
         .unwrap();
         generation_context.out.emit_end();
         generation_context.out.emit_end();
         generation_context.loop_depth -= 1;
      }
      Statement::Loop(bn) => {
         generation_context.loop_depth += 1;
         generation_context.out.emit_block_start(generation_context.loop_counter);
         generation_context.out.emit_loop_start(generation_context.loop_counter);
         generation_context.loop_counter += 1;
         for statement in &bn.statements {
            emit_statement(statement, generation_context, interner);
         }
         generation_context.out.emit_spaces();
         writeln!(
            generation_context.out.out,
            "br $l_{}",
            generation_context.loop_counter - generation_context.loop_depth
         )
         .unwrap();
         generation_context.out.emit_end();
         generation_context.out.emit_end();
         generation_context.loop_depth -= 1;
      }
      Statement::Break => {
         generation_context.out.emit_spaces();
         writeln!(
            generation_context.out.out,
            "br $b_{}",
            generation_context.loop_counter - generation_context.loop_depth
         )
         .unwrap();
      }
      Statement::Continue => {
         generation_context.out.emit_spaces();
         writeln!(
            generation_context.out.out,
            "br $l_{}",
            generation_context.loop_counter - generation_context.loop_depth
         )
         .unwrap();
      }
      Statement::Expression(en) => {
         do_emit(*en, generation_context, interner);
         for _ in 0..sizeof_type_values(
            generation_context.expressions[*en].exp_type.as_ref().unwrap(),
            generation_context.struct_size_info,
         ) {
            generation_context.out.emit_constant_instruction("drop");
         }
      }
      Statement::IfElse(en, block_1, block_2) => {
         do_emit_and_load_lval(*en, generation_context, interner);
         generation_context.out.emit_if_start(
            &ExpressionType::Value(ValueType::Unit),
            generation_context.enum_info,
            generation_context.struct_info,
         );
         // then
         generation_context.out.emit_then_start();
         for statement in &block_1.statements {
            emit_statement(statement, generation_context, interner);
         }
         generation_context.out.close();
         // else
         generation_context.out.emit_else_start();
         emit_statement(block_2, generation_context, interner);
         generation_context.out.close();
         // finish if
         generation_context.out.close();
      }
      Statement::Return(en) => {
         do_emit_and_load_lval(*en, generation_context, interner);

         adjust_stack_function_exit(generation_context);
         generation_context.out.emit_constant_instruction("return");
      }
   }
}

fn do_emit_and_load_lval(
   expr_index: ExpressionIndex,
   generation_context: &mut GenerationContext,
   interner: &mut Interner,
) {
   do_emit(expr_index, generation_context, interner);

   let expr_node = &generation_context.expressions[expr_index];
   if expr_node
      .expression
      .is_lvalue_disregard_consts(generation_context.expressions)
   {
      load(expr_node.exp_type.as_ref().unwrap(), generation_context);
   }
}

fn emit_literal_bytes(
   expr_index: ExpressionIndex,
   generation_context: &mut GenerationContext,
   interner: &mut Interner,
) {
   let expr_node = &generation_context.expressions[expr_index];
   match &expr_node.expression {
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(x) => {
         write!(generation_context.out.out, "\\{:02x}", *x as u8).unwrap();
      }
      Expression::EnumLiteral(name, variant) => {
         let width: u8 = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Enum(x)) => {
               let num_variants = generation_context.enum_info.get(x).unwrap().variants.len();
               if num_variants > u32::MAX as usize {
                  8
               } else if num_variants > u16::MAX as usize {
                  4
               } else if num_variants > u8::MAX as usize {
                  2
               } else {
                  1
               }
            }
            _ => unreachable!(),
         };
         let index = generation_context
            .enum_info
            .get(name)
            .unwrap()
            .variants
            .get_index_of(variant)
            .unwrap();
         generation_context.out.emit_spaces();
         for w in 0..width {
            let val = (index >> (8 * w)) & 0xff;
            write!(generation_context.out.out, "\\{:02x}", val).unwrap()
         }
      }
      Expression::IntLiteral(x) => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => x.width,
            ExpressionType::Pointer(_, _) => IntWidth::Pointer,
            _ => unreachable!(),
         }
         .as_num_bytes();
         for w in 0..width {
            let val = (x >> (8 * w)) & 0xff;
            write!(generation_context.out.out, "\\{:02x}", val).unwrap()
         }
      }
      Expression::FloatLiteral(x) => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Float(x)) => x.width,
            _ => unreachable!(),
         };
         match width {
            FloatWidth::Eight => {
               let bytes: u64 = x.to_bits();
               for w in 0..width.as_num_bytes() {
                  let val = (bytes >> (8 * w)) & 0xff;
                  write!(generation_context.out.out, "\\{:02x}", val).unwrap()
               }
            }
            FloatWidth::Four => {
               let bytes = (*x as f32).to_bits();
               for w in 0..width.as_num_bytes() {
                  let val = (bytes >> (8 * w)) & 0xff;
                  write!(generation_context.out.out, "\\{:02x}", val).unwrap()
               }
            }
         }
      }
      Expression::StringLiteral(str) => {
         let (offset, len) = generation_context.literal_offsets.get(str).unwrap();
         for w in 0..4 {
            let val = (*offset >> (8 * w)) & 0xff;
            write!(generation_context.out.out, "\\{:02x}", val).unwrap()
         }
         for w in 0..4 {
            let val = (*len >> (8 * w)) & 0xff;
            write!(generation_context.out.out, "\\{:02x}", val).unwrap()
         }
      }
      Expression::StructLiteral(s_name, fields) => {
         // We need to emit this in the proper order!!
         let map: HashMap<StrId, ExpressionIndex> = fields.iter().map(|x| (x.0, x.1)).collect();
         let si = generation_context.struct_info.get(s_name).unwrap();
         for field in si.field_types.iter() {
            let value_of_field = map.get(field.0).copied().unwrap();
            emit_literal_bytes(value_of_field, generation_context, interner);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            emit_literal_bytes(*expr, generation_context, interner);
         }
      }
      _ => unreachable!(),
   }
}

fn do_emit(expr_index: ExpressionIndex, generation_context: &mut GenerationContext, interner: &mut Interner) {
   let expr_node = &generation_context.expressions[expr_index];
   match &expr_node.expression {
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(x) => {
         generation_context.out.emit_const_i32(*x as u32);
      }
      Expression::EnumLiteral(name, variant) => {
         let wasm_type = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Enum(x)) => {
               let num_variants = generation_context.enum_info.get(x).unwrap().variants.len();
               if num_variants > u32::MAX as usize {
                  "i64"
               } else {
                  "i32"
               }
            }
            _ => unreachable!(),
         };
         let index = generation_context
            .enum_info
            .get(name)
            .unwrap()
            .variants
            .get_index_of(variant)
            .unwrap();
         generation_context.out.emit_spaces();
         writeln!(generation_context.out.out, "{}.const {}", wasm_type, index).unwrap();
      }
      Expression::IntLiteral(x) => {
         let wasm_type = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => match x.width {
               IntWidth::Eight => "i64",
               _ => "i32",
            },
            ExpressionType::Pointer(_, _) => "i32",
            _ => unreachable!(),
         };
         generation_context.out.emit_spaces();
         writeln!(generation_context.out.out, "{}.const {}", wasm_type, x).unwrap();
      }
      Expression::FloatLiteral(x) => {
         let wasm_type = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Float(x)) => match x.width {
               FloatWidth::Eight => "f64",
               FloatWidth::Four => "f32",
            },
            _ => unreachable!(),
         };
         generation_context.out.emit_spaces();
         writeln!(generation_context.out.out, "{}.const {}", wasm_type, x).unwrap();
      }
      Expression::StringLiteral(str) => {
         let (offset, len) = generation_context.literal_offsets.get(str).unwrap();
         generation_context.out.emit_const_i32(*offset);
         generation_context.out.emit_const_i32(*len);
      }
      Expression::BinaryOperator {
         operator: BinOp::LogicalAnd,
         lhs,
         rhs,
      } => {
         do_emit_and_load_lval(*lhs, generation_context, interner);
         generation_context.out.emit_if_start(
            &ExpressionType::Value(ValueType::Bool),
            generation_context.enum_info,
            generation_context.struct_info,
         );
         // then
         generation_context.out.emit_then_start();
         do_emit_and_load_lval(*rhs, generation_context, interner);
         generation_context.out.close();
         // else
         generation_context.out.emit_else_start();
         generation_context.out.emit_const_i32(0);
         generation_context.out.close();
         // finish if
         generation_context.out.close();
      }
      Expression::BinaryOperator {
         operator: BinOp::LogicalOr,
         lhs,
         rhs,
      } => {
         do_emit_and_load_lval(*lhs, generation_context, interner);
         generation_context.out.emit_if_start(
            &ExpressionType::Value(ValueType::Bool),
            generation_context.enum_info,
            generation_context.struct_info,
         );
         // then
         generation_context.out.emit_then_start();
         generation_context.out.emit_const_i32(1);
         generation_context.out.close();
         // else
         generation_context.out.emit_else_start();
         do_emit_and_load_lval(*rhs, generation_context, interner);
         generation_context.out.close();
         // finish if
         generation_context.out.close();
      }
      Expression::BinaryOperator { operator, lhs, rhs } => {
         do_emit_and_load_lval(*lhs, generation_context, interner);

         do_emit_and_load_lval(*rhs, generation_context, interner);

         let (wasm_type, suffix) = match generation_context.expressions[*lhs].exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => int_to_wasm_runtime_and_suffix(x),
            ExpressionType::Value(ValueType::Enum(x)) => {
               let num_variants = generation_context.enum_info.get(x).unwrap().variants.len();
               (if num_variants > u32::MAX as usize { "i64" } else { "i32" }, "_u")
            }
            ExpressionType::Value(ValueType::Float(x)) => match x.width {
               FloatWidth::Eight => ("f64", ""),
               FloatWidth::Four => ("f32", ""),
            },
            ExpressionType::Value(ValueType::Bool) => ("i32", "_u"),
            _ => unreachable!(),
         };
         generation_context.out.emit_spaces();
         match operator {
            BinOp::Add => {
               writeln!(generation_context.out.out, "{}.add", wasm_type).unwrap();
            }
            BinOp::Subtract => {
               writeln!(generation_context.out.out, "{}.sub", wasm_type).unwrap();
            }
            BinOp::Multiply => {
               writeln!(generation_context.out.out, "{}.mul", wasm_type).unwrap();
            }
            BinOp::Divide => {
               writeln!(generation_context.out.out, "{}.div{}", wasm_type, suffix).unwrap();
            }
            BinOp::Remainder => {
               writeln!(generation_context.out.out, "{}.rem{}", wasm_type, suffix).unwrap();
            }
            BinOp::Equality => {
               writeln!(generation_context.out.out, "{}.eq", wasm_type).unwrap();
            }
            BinOp::NotEquality => {
               writeln!(generation_context.out.out, "{}.ne", wasm_type).unwrap();
            }
            BinOp::GreaterThan => {
               writeln!(generation_context.out.out, "{}.gt{}", wasm_type, suffix).unwrap();
            }
            BinOp::GreaterThanOrEqualTo => {
               writeln!(generation_context.out.out, "{}.ge{}", wasm_type, suffix).unwrap();
            }
            BinOp::LessThan => {
               writeln!(generation_context.out.out, "{}.lt{}", wasm_type, suffix).unwrap();
            }
            BinOp::LessThanOrEqualTo => {
               writeln!(generation_context.out.out, "{}.le{}", wasm_type, suffix).unwrap();
            }
            BinOp::BitwiseAnd => {
               writeln!(generation_context.out.out, "{}.and", wasm_type).unwrap();
            }
            BinOp::BitwiseOr => {
               writeln!(generation_context.out.out, "{}.or", wasm_type).unwrap();
            }
            BinOp::BitwiseXor => {
               writeln!(generation_context.out.out, "{}.xor", wasm_type).unwrap();
            }
            BinOp::BitwiseLeftShift => {
               writeln!(generation_context.out.out, "{}.shl", wasm_type).unwrap();
            }
            BinOp::BitwiseRightShift => {
               writeln!(generation_context.out.out, "{}.shr{}", wasm_type, suffix).unwrap();
            }
            BinOp::LogicalAnd | BinOp::LogicalOr => unreachable!(),
         }
      }
      Expression::UnaryOperator(un_op, e_index) => {
         let get_wasm_type = || match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => match x.width {
               IntWidth::Eight => "i64",
               _ => "i32",
            },
            ExpressionType::Value(ValueType::Float(x)) => match x.width {
               FloatWidth::Eight => "f64",
               FloatWidth::Four => "f32",
            },
            ExpressionType::Value(ValueType::Bool) => "i32",
            ExpressionType::Pointer(_, _) => "i32",
            _ => unreachable!(),
         };

         let e = &generation_context.expressions[*e_index];

         match un_op {
            UnOp::AddressOf => {
               do_emit(*e_index, generation_context, interner);

               // This operator coaxes the lvalue to an rvalue without a load
            }
            UnOp::Dereference => {
               do_emit(*e_index, generation_context, interner);

               if e.expression.is_lvalue_disregard_consts(generation_context.expressions) {
                  load(e.exp_type.as_ref().unwrap(), generation_context);
               }
            }
            UnOp::Complement => {
               let wasm_type = get_wasm_type();
               do_emit_and_load_lval(*e_index, generation_context, interner);

               if *e.exp_type.as_ref().unwrap() == ExpressionType::Value(ValueType::Bool) {
                  generation_context.out.emit_spaces();
                  writeln!(generation_context.out.out, "{}.eqz", wasm_type).unwrap();
               } else {
                  complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
               }
            }
            UnOp::Negate => {
               let wasm_type = get_wasm_type();
               do_emit_and_load_lval(*e_index, generation_context, interner);

               match expr_node.exp_type.as_ref().unwrap() {
                  ExpressionType::Value(ValueType::Int(_)) | ExpressionType::Value(ValueType::Bool) => {
                     complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
                     generation_context.out.emit_spaces();
                     writeln!(generation_context.out.out, "{}.const 1", wasm_type).unwrap();
                     generation_context.out.emit_spaces();
                     writeln!(generation_context.out.out, "{}.add", wasm_type).unwrap();
                  }
                  ExpressionType::Value(ValueType::Float(_)) => {
                     writeln!(generation_context.out.out, "{}.neg", wasm_type).unwrap();
                  }
                  _ => unreachable!(),
               }
            }
         }
      }
      Expression::Extend(target_type, e) => {
         do_emit_and_load_lval(*e, generation_context, interner);

         let e = &generation_context.expressions[*e];

         let source_is_signed = match e.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => x.signed,
            ExpressionType::Value(ValueType::Bool) => false,
            _ => unreachable!(),
         };

         let suffix = if source_is_signed { "s" } else { "u" };

         match target_type {
            ExpressionType::Value(ValueType::Int(x)) if x.width == IntWidth::Eight => {
               generation_context.out.emit_spaces();
               writeln!(generation_context.out.out, "i64.extend_i32_{}", suffix).unwrap();
            }
            ExpressionType::Value(ValueType::Int(_)) => {
               // nop
            }
            _ => unreachable!(),
         }
      }
      Expression::Transmute(_target_type, e) => {
         do_emit_and_load_lval(*e, generation_context, interner);

         // nop, width is the same
      }
      Expression::Truncate(target_type, e) => {
         do_emit_and_load_lval(*e, generation_context, interner);

         let e = &generation_context.expressions[*e];

         if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Value(ValueType::Int(_)))
            && matches!(target_type, ExpressionType::Value(ValueType::Int(_)))
         {
            // int -> smaller int
            // 8bytes -> (4, 2, 1) bytes is a wrap
            // anything else is a nop

            // this is taking advantage of the fact that truncating is guaranteed to go downwards
            if sizeof_type_wasm(
               e.exp_type.as_ref().unwrap(),
               generation_context.enum_info,
               generation_context.struct_size_info,
            ) > 4
            {
               generation_context.out.emit_constant_instruction("i32.wrap_i64");
            }
         } else {
            // float -> int
            // i32.trunc_f32_s
            let (target_type_str, suffix) = match target_type {
               ExpressionType::Value(ValueType::Int(x)) => {
                  let base_str = match x.width {
                     IntWidth::Pointer => "i32",
                     IntWidth::Eight => "i64",
                     IntWidth::Four => "i32",
                     IntWidth::Two => "i16",
                     IntWidth::One => "i8",
                  };
                  (base_str, if x.signed { "_s" } else { "_u" })
               }
               _ => unreachable!(),
            };
            let dest_type_str = match e.exp_type.as_ref().unwrap() {
               ExpressionType::Value(ValueType::Float(x)) => match x.width {
                  FloatWidth::Eight => "f64",
                  FloatWidth::Four => "f32",
               },
               _ => unreachable!(),
            };
            generation_context.out.emit_spaces();
            writeln!(
               generation_context.out.out,
               "{}.trunc_sat_{}{}",
               target_type_str, dest_type_str, suffix
            )
            .unwrap();
         }
      }
      Expression::Variable(id) => {
         if let Some(v) = generation_context.static_addresses.get(id).copied() {
            generation_context.out.emit_const_i32(v);
         } else {
            get_stack_address_of_local(*id, generation_context);
         }
      }
      Expression::ProcedureCall {
         proc_name,
         args,
         generic_args: _generic_args,
      } => {
         for arg in args.iter() {
            do_emit_and_load_lval(arg.expr, generation_context, interner);
         }
         generation_context.out.emit_call(*proc_name, interner);
      }
      Expression::StructLiteral(s_name, fields) => {
         // First we emit the expressions *in the order they were written*,
         // storing them into temps
         for field in fields.iter() {
            let field_virual_var = interner.reverse_lookup(&format!("::{}", field.1.index()));
            get_stack_address_of_local(field_virual_var, generation_context);
            do_emit_and_load_lval(field.1, generation_context, interner);
            store(
               generation_context.expressions[field.1].exp_type.as_ref().unwrap(),
               generation_context,
               interner,
            );
         }

         // Then we load from the temps in the order the struct is laid out
         let map: HashMap<StrId, ExpressionIndex> = fields.iter().map(|x| (x.0, x.1)).collect();
         let si = generation_context.struct_info.get(s_name).unwrap();
         for field in si.field_types.iter() {
            let value_of_field = map.get(field.0).copied().unwrap();
            let field_virual_var = interner.reverse_lookup(&format!("::{}", value_of_field.index()));
            get_stack_address_of_local(field_virual_var, generation_context);
            load(field.1, generation_context);
         }
      }
      Expression::FieldAccess(field_names, lhs) => {
         do_emit(*lhs, generation_context, interner);

         let lhs = &generation_context.expressions[*lhs];

         if lhs
            .expression
            .is_lvalue_disregard_consts(generation_context.expressions)
         {
            let mut si = match lhs.exp_type.as_ref() {
               Some(ExpressionType::Value(ValueType::Struct(x))) => generation_context.struct_info.get(x).unwrap(),
               _ => unreachable!(),
            };
            let mut mem_offset = 0;

            for field_name in field_names.iter().take(field_names.len() - 1) {
               for field in si.field_types.iter() {
                  if field.0 == field_name {
                     si = match field.1 {
                        ExpressionType::Value(ValueType::Struct(x)) => generation_context.struct_info.get(x).unwrap(),
                        _ => unreachable!(),
                     };
                     break;
                  }

                  mem_offset += sizeof_type_mem(
                     field.1,
                     generation_context.enum_info,
                     generation_context.struct_size_info,
                  );
               }
            }

            for field in si.field_types.iter() {
               if field.0 == field_names.last().unwrap() {
                  break;
               }

               mem_offset += sizeof_type_mem(
                  field.1,
                  generation_context.enum_info,
                  generation_context.struct_size_info,
               );
            }

            generation_context.out.emit_const_add_i32(mem_offset);
         } else {
            let mut current_struct_name = match lhs.exp_type.as_ref() {
               Some(ExpressionType::Value(ValueType::Struct(x))) => x,
               _ => unreachable!(),
            };

            // We have the entire struct sitting on the value stack
            // -- there's no "pick" operation in wasm so we can't just choose the fields we want
            // instead we call these special functions which basically convert the struct fields into locals so we can select them easier
            // yeah, this is a pretty big hack
            for field_name in field_names.iter().take(field_names.len() - 1) {
               let func_name = interner.intern(&format!(
                  "::struct::{}::{}",
                  interner.lookup(*current_struct_name),
                  interner.lookup(*field_name)
               ));
               generation_context.out.emit_call(func_name, interner);
               current_struct_name = match generation_context
                  .struct_info
                  .get(current_struct_name)
                  .unwrap()
                  .field_types
                  .get(field_name)
               {
                  Some(ExpressionType::Value(ValueType::Struct(x))) => x,
                  _ => unreachable!(),
               };
            }

            let func_name = interner.intern(&format!(
               "::struct::{}::{}",
               interner.lookup(*current_struct_name),
               interner.lookup(*field_names.last().unwrap())
            ));
            generation_context.out.emit_call(func_name, interner);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            do_emit_and_load_lval(*expr, generation_context, interner);
         }
      }
      Expression::ArrayIndex { array, index } => {
         fn calculate_offset(
            array: ExpressionIndex,
            index_e: ExpressionIndex,
            generation_context: &mut GenerationContext,
            interner: &mut Interner,
         ) {
            let sizeof_inner = match &generation_context.expressions[array].exp_type {
               Some(ExpressionType::Value(ValueType::Array(x, _))) => {
                  sizeof_type_mem(&*x, generation_context.enum_info, generation_context.struct_size_info)
               }
               _ => unreachable!(),
            };

            if let Expression::IntLiteral(x) = generation_context.expressions[index_e].expression {
               // Safe assert due to inference and constant folding validating this
               let val_32 = u32::try_from(x).unwrap();
               let result = sizeof_inner.wrapping_mul(val_32);
               // This won't emit anything if result == 0
               generation_context.out.emit_const_add_i32(result);
            } else {
               do_emit_and_load_lval(index_e, generation_context, interner);
               generation_context.out.emit_const_mul_i32(sizeof_inner);
               generation_context.out.emit_constant_instruction("i32.add");
            }
         }

         if generation_context.expressions[*array]
            .expression
            .is_lvalue_disregard_consts(generation_context.expressions)
         {
            do_emit(*array, generation_context, interner);
            calculate_offset(*array, *index, generation_context, interner);
         } else {
            let array_var_id = interner.reverse_lookup(&format!("::{}", array.index()));

            // spill to the virtual variable
            get_stack_address_of_local(array_var_id, generation_context);
            do_emit(*array, generation_context, interner);
            store(
               generation_context.expressions[*array].exp_type.as_ref().unwrap(),
               generation_context,
               interner,
            );

            // Now that we've spilled, we can proceed to load like normal
            get_stack_address_of_local(array_var_id, generation_context);
            calculate_offset(*array, *index, generation_context, interner);

            // ...but we're an rvalue, so we have to load
            load(expr_node.exp_type.as_ref().unwrap(), generation_context);
         }
      }
   }
}

fn complement_val(t_type: &ExpressionType, wasm_type: &str, generation_context: &mut GenerationContext) {
   let magic_const: u64 = match t_type {
      ExpressionType::Value(crate::type_data::U8_TYPE) => std::u8::MAX as u64,
      ExpressionType::Value(crate::type_data::U16_TYPE) => std::u16::MAX as u64,
      ExpressionType::Value(crate::type_data::U32_TYPE) => std::u32::MAX as u64,
      // @FixedPointerWidth
      ExpressionType::Value(crate::type_data::USIZE_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::U64_TYPE) => std::u64::MAX,
      ExpressionType::Value(crate::type_data::I8_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::I16_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::I32_TYPE) => std::u32::MAX as u64,
      // @FixedPointerWidth
      ExpressionType::Value(crate::type_data::ISIZE_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::I64_TYPE) => std::u64::MAX,
      _ => unreachable!(),
   };
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "{}.const {}", wasm_type, magic_const).unwrap();
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "{}.xor", wasm_type).unwrap();
}

/// Places the address of given local on the stack
fn get_stack_address_of_local(id: StrId, generation_context: &mut GenerationContext) {
   let offset = generation_context.local_offsets_mem.get(&id).copied().unwrap();
   generation_context.out.emit_get_global("bp");
   generation_context.out.emit_const_add_i32(offset);
}

fn load(val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   if sizeof_type_values(val_type, generation_context.struct_size_info) > 1 {
      generation_context.out.emit_set_global("mem_address");
      complex_load(0, val_type, generation_context);
   } else {
      simple_load(val_type, generation_context);
   }
}

fn complex_load(mut offset: u32, val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   match val_type {
      ExpressionType::Value(ValueType::Struct(x)) => {
         for field in generation_context.struct_info.get(x).unwrap().field_types.values() {
            match sizeof_type_values(field, generation_context.struct_size_info).cmp(&1) {
               std::cmp::Ordering::Less => (),
               std::cmp::Ordering::Equal => {
                  generation_context.out.emit_get_global("mem_address");
                  generation_context.out.emit_const_add_i32(offset);
                  simple_load(field, generation_context);
               }
               std::cmp::Ordering::Greater => complex_load(offset, field, generation_context),
            }

            offset += sizeof_type_mem(field, generation_context.enum_info, generation_context.struct_size_info);
         }
      }
      ExpressionType::Value(ValueType::Array(a_type, len)) => {
         for _ in 0..*len {
            match sizeof_type_values(a_type, generation_context.struct_size_info).cmp(&1) {
               std::cmp::Ordering::Less => (),
               std::cmp::Ordering::Equal => {
                  generation_context.out.emit_get_global("mem_address");
                  generation_context.out.emit_const_add_i32(offset);
                  simple_load(a_type, generation_context);
               }
               std::cmp::Ordering::Greater => {
                  complex_load(offset, a_type, generation_context);
               }
            }

            offset += sizeof_type_mem(
               a_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            );
         }
      }
      _ => unreachable!(),
   }
}

fn simple_load(val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   if sizeof_type_values(val_type, generation_context.struct_size_info) == 0 {
      // Drop the load address; nothing to load
      generation_context.out.emit_constant_instruction("drop");
   } else if sizeof_type_mem(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) == sizeof_type_wasm(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) {
      generation_context.out.emit_spaces();
      type_to_s(
         val_type,
         &mut generation_context.out.out,
         generation_context.enum_info,
         generation_context.struct_info,
      );
      writeln!(generation_context.out.out, ".load").unwrap();
   } else {
      let (load_suffx, sign_suffix) = match val_type {
         ExpressionType::Value(ValueType::Int(x)) => {
            let load_suffx = match x.width {
               IntWidth::Eight => "64",
               IntWidth::Four | IntWidth::Pointer => "32",
               IntWidth::Two => "16",
               IntWidth::One => "8",
            };
            let sign_suffix = if x.signed { "_s" } else { "_u" };
            (load_suffx, sign_suffix)
         }
         ExpressionType::Value(ValueType::Enum(x)) => {
            let num_variants = generation_context.enum_info.get(x).unwrap().variants.len();
            (
               if num_variants > u32::MAX as usize {
                  "64"
               } else if num_variants > u16::MAX as usize {
                  "32"
               } else if num_variants > u8::MAX as usize {
                  "16"
               } else {
                  "8"
               },
               "_u",
            )
         }
         ExpressionType::Value(ValueType::Float(_)) => ("", ""),
         ExpressionType::Value(ValueType::Bool) => ("8", "_u"),
         _ => unreachable!(),
      };
      generation_context.out.emit_spaces();
      type_to_s(
         val_type,
         &mut generation_context.out.out,
         generation_context.enum_info,
         generation_context.struct_info,
      );
      writeln!(generation_context.out.out, ".load{}{}", load_suffx, sign_suffix).unwrap();
   }
}

fn store(val_type: &ExpressionType, generation_context: &mut GenerationContext, interner: &mut Interner) {
   if sizeof_type_values(val_type, generation_context.struct_size_info) == 0 {
      // drop the placement address
      generation_context.out.emit_constant_instruction("drop");
   } else if sizeof_type_values(val_type, generation_context.struct_size_info) == 1 {
      simple_store(val_type, generation_context);
   } else if sizeof_type_values(val_type, generation_context.struct_size_info) > 1 {
      let (store_fcn_index, _) = generation_context.needed_store_fns.insert_full(val_type.clone());
      generation_context
         .out
         .emit_call(interner.intern(&format!("::store::{}", store_fcn_index)), interner);
   }
}

// VALUE STACK: i32 MEMORY_OFFSET, (any 1 value)
fn simple_store(val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   // If this is a tiny struct or array, drill into the inner type
   match val_type {
      ExpressionType::Value(ValueType::Struct(x)) => {
         let si = generation_context.struct_info.get(x).unwrap();
         // Find the first non-zero-sized struct field and store that
         // (there should only be one if we're in simple_store)
         for (_, field_type) in si.field_types.iter() {
            match sizeof_type_values(field_type, generation_context.struct_size_info) {
               0 => continue,
               1 => return simple_store(field_type, generation_context),
               _ => unreachable!(),
            }
         }
      }
      ExpressionType::Value(ValueType::Array(inner_type, _len)) => {
         return simple_store(inner_type, generation_context);
      }
      _ => (),
   }
   if sizeof_type_mem(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) == sizeof_type_wasm(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) {
      generation_context.out.emit_spaces();
      type_to_s(
         val_type,
         &mut generation_context.out.out,
         generation_context.enum_info,
         generation_context.struct_info,
      );
      writeln!(generation_context.out.out, ".store").unwrap();
   } else {
      let load_suffx = match val_type {
         ExpressionType::Value(ValueType::Int(x)) => match x.width {
            IntWidth::Eight => "64",
            IntWidth::Four | IntWidth::Pointer => "32",
            IntWidth::Two => "16",
            IntWidth::One => "8",
         },
         ExpressionType::Value(ValueType::Enum(x)) => {
            let num_variants = generation_context.enum_info.get(x).unwrap().variants.len();
            if num_variants > u32::MAX as usize {
               "64"
            } else if num_variants > u16::MAX as usize {
               "32"
            } else if num_variants > u8::MAX as usize {
               "16"
            } else {
               "8"
            }
         }
         ExpressionType::Value(ValueType::Float(_)) => "",
         ExpressionType::Value(ValueType::Bool) => "8",
         _ => unreachable!(),
      };
      generation_context.out.emit_spaces();
      type_to_s(
         val_type,
         &mut generation_context.out.out,
         generation_context.enum_info,
         generation_context.struct_info,
      );
      writeln!(generation_context.out.out, ".store{}", load_suffx,).unwrap();
   }
}

fn adjust_stack_function_entry(generation_context: &mut GenerationContext) {
   if generation_context.sum_sizeof_locals_mem == MINIMUM_STACK_FRAME_SIZE {
      return;
   }

   generation_context.out.emit_get_global("sp");
   generation_context.out.emit_get_global("bp");
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "i32.store").unwrap();
   generation_context.out.emit_get_global("sp");
   generation_context.out.emit_set_global("bp");
   adjust_stack(generation_context, "add");
}

fn adjust_stack_function_exit(generation_context: &mut GenerationContext) {
   if generation_context.sum_sizeof_locals_mem == MINIMUM_STACK_FRAME_SIZE {
      return;
   }

   adjust_stack(generation_context, "sub");
   generation_context.out.emit_get_global("sp");
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "i32.load").unwrap();
   generation_context.out.emit_set_global("bp");
}

fn adjust_stack(generation_context: &mut GenerationContext, instr: &str) {
   generation_context.out.emit_get_global("sp");
   // ensure that each stack frame is strictly aligned so that internal stack frame alignment is preserved
   let adjust_value = aligned_address(generation_context.sum_sizeof_locals_mem, 8);
   generation_context.out.emit_const_i32(adjust_value);
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "i32.{}", instr).unwrap();
   generation_context.out.emit_set_global("sp");
}
