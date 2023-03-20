use std::collections::HashMap;
use std::fmt::Display;
use std::io::Write;

use indexmap::{IndexMap, IndexSet};
use wasm_encoder::{
   ConstExpr, ElementSection, EntityType, ExportSection, FunctionSection, GlobalSection, GlobalType, ImportSection,
   Instruction, MemArg, MemorySection, MemoryType, Module, RefType, TableSection, TableType, TypeSection, ValType, BlockType, DataSection,
};

use crate::add_virtual_variables::is_wasm_compatible_rval_transmute;
use crate::interner::{Interner, StrId};
use crate::parse::{
   statement_always_returns, BinOp, CastType, Expression, ExpressionId, ExpressionPool, ExternalProcImplSource,
   ProcedureDefinition, Program, Statement, StatementNode, UnOp, VariableId,
};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::{
   aligned_address, mem_alignment, sizeof_type_mem, sizeof_type_values, sizeof_type_wasm, SizeInfo,
};
use crate::type_data::{ExpressionType, FloatWidth, IntType, IntWidth, F32_TYPE, F64_TYPE};
use crate::Target;

const MINIMUM_STACK_FRAME_SIZE: u32 = 4;

// globals
const SP: u32 = 0;
const BP: u32 = 1;
const MEM_ADDRESS: u32 = 2;

struct GenerationContext<'a> {
   out: PrettyWasmWriter,
   active_fcn: wasm_encoder::Function,
   type_manager: TypeManager,
   literal_offsets: HashMap<StrId, (u32, u32)>,
   static_addresses: HashMap<VariableId, u32>,
   local_offsets_mem: HashMap<VariableId, u32>,
   struct_info: &'a IndexMap<StrId, StructInfo>,
   struct_size_info: &'a HashMap<StrId, SizeInfo>,
   enum_info: &'a IndexMap<StrId, EnumInfo>,
   needed_store_fns: IndexSet<ExpressionType>,
   sum_sizeof_locals_mem: u32,
   expressions: &'a ExpressionPool,
   procedure_to_table_index: IndexSet<StrId>,
   indirect_callees: Vec<ExpressionId>,
}

struct PrettyWasmWriter {
   out: Vec<u8>,
}

impl PrettyWasmWriter {
   fn close(&mut self) {
      writeln!(self.out, ")").unwrap();
   }

   fn emit_function_start<'a, I>(
      &mut self,
      name: StrId,
      params: I,
      result_type: &ExpressionType,
      si: &IndexMap<StrId, StructInfo>,
      interner: &Interner,
   ) where
      I: IntoIterator<Item = &'a ExpressionType>,
   {
      write!(self.out, "(func ${}", interner.lookup(name)).unwrap();
      for param in params {
         self.out.push(b' ');
         write_type_as_params(param, &mut self.out, si);
      }
      self.out.push(b' ');
      write_type_as_result(result_type, &mut self.out, si);
      self.out.push(b'\n');
   }

   fn emit_function_type<'a, I>(
      &mut self,
      name: ExpressionId,
      params: I,
      result_type: &ExpressionType,
      si: &IndexMap<StrId, StructInfo>,
   ) where
      I: IntoIterator<Item = &'a ExpressionType>,
   {
      write!(self.out, "(type $::{} (func", name.0).unwrap();
      for param in params {
         self.out.push(b' ');
         write_type_as_params(param, &mut self.out, si);
      }
      self.out.push(b' ');
      write_type_as_result(result_type, &mut self.out, si);
      self.out.push(b')');
      self.out.push(b')');
      self.out.push(b'\n');
   }

   fn emit_store_function_start(&mut self, index: usize, param: &ExpressionType, si: &IndexMap<StrId, StructInfo>) {
      write!(self.out, "(func $::store::{} (param i32) ", index).unwrap();
      write_type_as_params(param, &mut self.out, si);
      self.out.push(b'\n');
   }

   fn emit_block_start(&mut self, block_name: &'static str, label_val: u64) {
      writeln!(self.out, "block ${}_{}", block_name, label_val).unwrap();
   }

   fn emit_loop_start(&mut self, label_val: u64) {
      writeln!(self.out, "loop $l_{}", label_val).unwrap();
   }

   fn emit_end(&mut self) {
      writeln!(self.out, "end").unwrap();
   }

   fn emit_if_start(&mut self, result_type: &ExpressionType, si: &IndexMap<StrId, StructInfo>) {
      write!(self.out, "(if ").unwrap();
      write_type_as_result(result_type, &mut self.out, si);
      self.out.push(b'\n');
   }

   fn emit_then_start(&mut self) {
      writeln!(self.out, "(then ").unwrap();
   }

   fn emit_else_start(&mut self) {
      writeln!(self.out, "(else ").unwrap();
   }

   fn emit_data(&mut self, mem_index: u32, offset: u32, literal: &str) {
      write!(self.out, "(data {} (i32.const {}) \"", mem_index, offset).unwrap();
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

   fn emit_call(&mut self, func_name: StrId, interner: &Interner) {
      writeln!(self.out, "call ${}", interner.lookup(func_name)).unwrap();
   }
}

impl GenerationContext<'_> {
   fn emit_const_add_i32(&mut self, value: u32) {
      if value > 0 {
         self.active_fcn.instruction(&Instruction::I32Const(value as i32));
         self.active_fcn.instruction(&Instruction::I32Add);
      }
   }

   fn emit_const_mul_i32(&mut self, value: u32) {
      if value != 1 {
         self.active_fcn.instruction(&Instruction::I32Const(value as i32));
         self.active_fcn.instruction(&Instruction::I32Mul);
      }
   }
}

fn write_type_as_result(t: &ExpressionType, out: &mut Vec<u8>, si: &IndexMap<StrId, StructInfo>) {
   let mut type_buf = vec![];
   type_to_wasm_type(t, &mut type_buf, si);
   for wt in type_buf.iter() {
      write!(out, "(result {}) ", *wt).unwrap();
   }
   if !type_buf.is_empty() {
      let _ = out.pop();
   }
}

fn definition_to_type(def: &ProcedureDefinition, si: &IndexMap<StrId, StructInfo>) -> (Vec<ValType>, Vec<ValType>) {
   let mut param_type_buf = vec![];
   for param in def.parameters.iter() {
      type_to_wasm_type(&param.p_type.e_type, &mut param_type_buf, si);
   }
   let mut return_type_buf = vec![];
   type_to_wasm_type(&def.ret_type.e_type, &mut return_type_buf, si);
   (
      param_type_buf.into_iter().map(|x| x.into()).collect(),
      return_type_buf.into_iter().map(|x| x.into()).collect(),
   )
}

fn write_type_as_params(t: &ExpressionType, out: &mut Vec<u8>, si: &IndexMap<StrId, StructInfo>) {
   let mut type_buf = vec![];
   type_to_wasm_type(t, &mut type_buf, si);
   for wt in type_buf.iter() {
      write!(out, "(param {}) ", *wt).unwrap();
   }
   if !type_buf.is_empty() {
      let _ = out.pop();
   }
}

#[derive(Copy, Clone)]
enum WasmType {
   Int64,
   Int32,
   Float64,
   Float32,
}

impl WasmType {
   fn store_instruction(&self) -> Instruction {
      match self {
         WasmType::Int64 => Instruction::I64Store(null_mem_arg()),
         WasmType::Int32 => Instruction::I32Store(null_mem_arg()),
         WasmType::Float64 => Instruction::F64Store(null_mem_arg()),
         WasmType::Float32 => Instruction::F32Store(null_mem_arg()),
      }
   }
}

impl Display for WasmType {
   fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      f.write_str(match self {
         WasmType::Int64 => "i64",
         WasmType::Int32 => "i32",
         WasmType::Float64 => "f64",
         WasmType::Float32 => "f32",
      })
   }
}

//nocheckin just get rid of WasmType
impl Into<ValType> for WasmType {
   fn into(self) -> ValType {
      match self {
         WasmType::Int64 => ValType::I64,
         WasmType::Int32 => ValType::I32,
         WasmType::Float64 => ValType::F64,
         WasmType::Float32 => ValType::F32,
      }
   }
}

fn type_to_wasm_type(t: &ExpressionType, buf: &mut Vec<WasmType>, si: &IndexMap<StrId, StructInfo>) {
   match t {
      ExpressionType::Unit | ExpressionType::Never | ExpressionType::ProcedureItem(_, _) => (),
      ExpressionType::Struct(x) => {
         let field_types = &si.get(x).unwrap().field_types;
         for e_type_node in field_types.values() {
            type_to_wasm_type(&e_type_node.e_type, buf, si);
         }
      }
      ExpressionType::Array(a_type, len) => {
         for _ in 0..*len {
            type_to_wasm_type(a_type, buf, si);
         }
      }
      _ => buf.push(type_to_wasm_type_basic(t)),
   }
}

fn type_to_wasm_type_basic(t: &ExpressionType) -> WasmType {
   match t {
      ExpressionType::Pointer(_) => WasmType::Int32,
      ExpressionType::Int(x) => match x.width {
         IntWidth::Eight => WasmType::Int64,
         _ => WasmType::Int32,
      },
      ExpressionType::Float(x) => match x.width {
         FloatWidth::Eight => WasmType::Float64,
         FloatWidth::Four => WasmType::Float32,
      },
      ExpressionType::Bool => WasmType::Int32,
      ExpressionType::ProcedurePointer { .. } => WasmType::Int32,
      _ => unreachable!(),
   }
}

fn int_to_wasm_runtime_and_suffix(x: IntType) -> (WasmType, &'static str) {
   let wasm_type = match x.width {
      IntWidth::Eight => WasmType::Int64,
      _ => WasmType::Int32,
   };
   let suffix = if x.signed { "_s" } else { "_u" };
   (wasm_type, suffix)
}

fn dynamic_move_locals_of_type_to_dest(
   memory_lookup: &Instruction,
   offset: &mut u32,
   local_index: &mut u32,
   field: &ExpressionType,
   generation_context: &mut GenerationContext,
) {
   if sizeof_type_values(field, generation_context.enum_info, generation_context.struct_size_info) == 0 {
      // Nothing to move
      return;
   }

   match field {
      ExpressionType::Struct(x) => {
         for (sub_field, next_sub_field) in generation_context.struct_info.get(x).unwrap().field_types.values().zip(
            generation_context
               .struct_info
               .get(x)
               .unwrap()
               .field_types
               .values()
               .skip(1),
         ) {
            dynamic_move_locals_of_type_to_dest(
               memory_lookup,
               offset,
               local_index,
               &sub_field.e_type,
               generation_context,
            );
            let alignment_of_next = mem_alignment(
               &next_sub_field.e_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            );
            let this_size = sizeof_type_mem(
               &sub_field.e_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            );
            // we've already accounted for the size, but adding padding if necessary
            *offset += aligned_address(this_size, alignment_of_next) - this_size;
         }

         if let Some(last_sub_field) = generation_context
            .struct_info
            .get(x)
            .unwrap()
            .field_types
            .values()
            .last()
         {
            dynamic_move_locals_of_type_to_dest(
               memory_lookup,
               offset,
               local_index,
               &last_sub_field.e_type,
               generation_context,
            );
            let alignment_of_next = generation_context.struct_size_info.get(x).unwrap().strictest_alignment;
            let this_size = sizeof_type_mem(
               &last_sub_field.e_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            );
            // we've already accounted for the size, but adding padding if necessary
            *offset += aligned_address(this_size, alignment_of_next) - this_size;
         }
      }
      ExpressionType::Array(inner_type, a_len) => {
         for _ in 0..*a_len {
            dynamic_move_locals_of_type_to_dest(memory_lookup, offset, local_index, inner_type, generation_context);
         }
      }
      _ => {
         generation_context.active_fcn.instruction(memory_lookup);
         generation_context.emit_const_add_i32(*offset);
         generation_context
            .active_fcn
            .instruction(&Instruction::LocalGet(*local_index));
         simple_store(field, generation_context);
         *local_index += 1;
         *offset += sizeof_type_mem(field, generation_context.enum_info, generation_context.struct_size_info);
      }
   }
}

struct TypeManager {
   num_registered_types: u32,
}

impl TypeManager {
   fn new() -> TypeManager {
      TypeManager { num_registered_types: 0 }
   }

   fn register_or_find_type(&mut self, def: &ProcedureDefinition, si: &IndexMap<StrId, StructInfo>, type_section: &mut TypeSection) -> u32 {
      definition_to_type(def, si);
      let old = self.num_registered_types;
      self.num_registered_types += 1;
      old
   }
}

// MEMORY LAYOUT
// 0-l literals
// l-s statics
// s+ program stack (local variables and parameters are pushed here during runtime)
pub fn emit_wasm(
   program: &mut Program,
   interner: &mut Interner,
   expressions: &ExpressionPool,
   target: Target,
) -> Vec<u8> {
   let mut generation_context = GenerationContext {
      out: PrettyWasmWriter { out: Vec::new() },
      active_fcn: wasm_encoder::Function::new_with_locals_types([]),
      type_manager: TypeManager::new(),
      literal_offsets: HashMap::with_capacity(program.literals.len()),
      static_addresses: HashMap::with_capacity(program.global_info.len()),
      local_offsets_mem: HashMap::new(),
      needed_store_fns: IndexSet::new(),
      struct_info: &program.struct_info,
      struct_size_info: &program.struct_size_info,
      enum_info: &program.enum_info,
      sum_sizeof_locals_mem: 0,
      expressions,
      procedure_to_table_index: IndexSet::new(),
      indirect_callees: Vec::new(),
   };

   let mut type_section = TypeSection::new();

   let mut import_section = ImportSection::new();
   let mut export_section = ExportSection::new();
   let mut function_section = FunctionSection::new();
   let mut memory_section = MemorySection::new();
   let mut data_section = DataSection::new();

   let mut num_procedures: u32 = 0;
   for external_procedure in program
      .external_procedures
      .iter()
      .filter(|x| std::mem::discriminant(&x.impl_source) == std::mem::discriminant(&ExternalProcImplSource::External))
   {
      let type_index = generation_context.type_manager.register_or_find_type(&external_procedure.definition, generation_context.struct_info, &mut type_section);
      match target {
         Target::Lib => (),
         Target::Wasm4 | Target::Microw8 => {
            import_section.import(
               "env",
               interner.lookup(external_procedure.definition.name),
               EntityType::Function(type_index),
            );
         }
         Target::Wasi => {
            import_section.import(
               "wasi_unstable",
               interner.lookup(external_procedure.definition.name),
               EntityType::Function(type_index),
            );
         }
      }
      num_procedures += 1;
   }

   // target specific imports/exports
   match target {
      Target::Lib => (),
      Target::Wasm4 => {
         import_section.import(
            "env",
            "memory",
            EntityType::Memory(MemoryType {
               minimum: 1,
               maximum: Some(1),
               memory64: false,
               shared: false,
            }),
         );
         export_section.export("update", wasm_encoder::ExportKind::Func, todo!());
         if program.procedure_info.contains_key(&interner.intern("start")) {
            export_section.export("start", wasm_encoder::ExportKind::Func, todo!());
         }
      }
      Target::Microw8 => {
         import_section.import(
            "env",
            "memory",
            EntityType::Memory(MemoryType {
               minimum: 4,
               maximum: Some(4),
               memory64: false,
               shared: false,
            }),
         );
         export_section.export("upd", wasm_encoder::ExportKind::Func, todo!());
         if program.procedure_info.contains_key(&interner.intern("snd")) {
            export_section.export("snd", wasm_encoder::ExportKind::Func, todo!());
         }
      }
      Target::Wasi => {
         memory_section.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
         });
         export_section.export("memory", wasm_encoder::ExportKind::Memory, 0);
         export_section.export("_start", wasm_encoder::ExportKind::Func, todo!());
      }
   }

   // Data section

   // the base memory offset varies per platform;
   // on wasm-4/microw8, we don't own all of the memory!
   let mut offset: u32 = match target {
      Target::Wasi | Target::Lib => 0x0,
      Target::Wasm4 => 0x19a0,
      Target::Microw8 => 0x14000,
   };

   for s in program.literals.iter() {
      let str_value = interner.lookup(*s);
      data_section.active(0, &ConstExpr::i32_const(offset as i32), str_value.as_bytes().iter().copied());
      //TODO: and here truncation
      let s_len = str_value.len() as u32;
      generation_context.literal_offsets.insert(*s, (offset, s_len));
      // TODO: check for overflow here
      offset += s_len;
   }

   // Handle alignment of statics
   {
      program
         .global_info
         .sort_by(|_k_1, v_1, _k_2, v_2| compare_type_alignment(&v_1.expr_type, &v_2.expr_type, &generation_context));

      let strictest_alignment = if let Some(v) = program.global_info.first() {
         mem_alignment(
            &v.1.expr_type,
            generation_context.enum_info,
            generation_context.struct_size_info,
         )
      } else {
         1
      };

      offset = aligned_address(offset, strictest_alignment);
   }
   // what ridiculous crap. we need to get rid of this map.
   let mut static_addresses_by_name = HashMap::new();
   for (static_var, static_details) in program.global_info.iter() {
      debug_assert!(!static_details.is_const);
      generation_context.static_addresses.insert(*static_var, offset);
      static_addresses_by_name.insert(static_details.name, offset);

      offset += sizeof_type_mem(
         &static_details.expr_type,
         generation_context.enum_info,
         generation_context.struct_size_info,
      );
   }

   let mut buf = vec![];
   for p_static in program.statics.iter().filter(|x| x.value.is_some()) {
      emit_literal_bytes(&mut buf, p_static.value.unwrap(), &mut generation_context);
      let static_address = static_addresses_by_name.get(&p_static.name.str).copied().unwrap();
      data_section.active(0, &ConstExpr::i32_const(static_address as i32), buf.drain(..));
   }

   // keep stack aligned
   offset = aligned_address(offset, 8);

   let global_section = {
      let mut globals = GlobalSection::new();
      globals.global(
         GlobalType {
            val_type: wasm_encoder::ValType::I32,
            mutable: true,
         },
         &ConstExpr::i32_const(offset as i32),
      ); // sp
      globals.global(
         GlobalType {
            val_type: wasm_encoder::ValType::I32,
            mutable: true,
         },
         &ConstExpr::i32_const(offset as i32),
      ); // bp
      globals.global(
         GlobalType {
            val_type: wasm_encoder::ValType::I32,
            mutable: true,
         },
         &ConstExpr::i32_const(0),
      ); // mem_address

      globals
   };

   for external_procedure in program
      .external_procedures
      .iter()
      .filter(|x| std::mem::discriminant(&x.impl_source) == std::mem::discriminant(&ExternalProcImplSource::Builtin))
   {
      let proc_name = interner.lookup(external_procedure.definition.name);
      if proc_name == "sizeof" || proc_name == "alignof" || proc_name == "num_variants" {
         // These builtins have no body. All calls should have been lowered.
         continue;
      }

      generation_context.out.emit_function_start(
         external_procedure.definition.name,
         external_procedure
            .definition
            .parameters
            .iter()
            .map(|x| &x.p_type.e_type),
         &external_procedure.definition.ret_type.e_type,
         &program.struct_info,
         interner,
      );

      match interner.lookup(external_procedure.definition.name) {
         "wasm_memory_size" => {
            generation_context.active_fcn.instruction(&Instruction::MemorySize(0));
         }
         "wasm_memory_grow" => {
            generation_context.active_fcn.instruction(&Instruction::LocalGet(0));
            generation_context.active_fcn.instruction(&Instruction::MemoryGrow(0));
         }
         "sqrt" => {
            generation_context.active_fcn.instruction(&Instruction::LocalGet(0));
            generation_context.active_fcn.instruction(&Instruction::F64Sqrt);
         }
         "sqrt_32" => {
            generation_context.active_fcn.instruction(&Instruction::LocalGet(0));
            generation_context.active_fcn.instruction(&Instruction::F32Sqrt);
         }
         "unreachable" => {
            generation_context.active_fcn.instruction(&Instruction::Unreachable);
         }
         x => {
            panic!("Unimplemented builtin: {}", x);
         }
      }
      generation_context.out.close();
   }

   for procedure in program.procedures.iter_mut() {
      if !procedure.definition.generic_parameters.is_empty() {
         continue;
      }

      generation_context.local_offsets_mem.clear();

      // 0-4 == value of previous frame base pointer
      generation_context.sum_sizeof_locals_mem = MINIMUM_STACK_FRAME_SIZE;

      let mut mem_info: IndexMap<VariableId, (u32, u32)> = procedure
         .locals
         .iter()
         .map(|x| {
            let alignment = mem_alignment(x.1, generation_context.enum_info, generation_context.struct_size_info);
            let size = sizeof_type_mem(x.1, generation_context.enum_info, generation_context.struct_size_info);
            (*x.0, (alignment, size))
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

      generation_context.out.emit_function_start(
         procedure.definition.name,
         procedure.definition.parameters.iter().map(|x| &x.p_type.e_type),
         &procedure.definition.ret_type.e_type,
         &program.struct_info,
         interner,
      );

      adjust_stack_function_entry(&mut generation_context);

      // Copy parameters to stack memory so we can take pointers
      let mut values_index = 0;
      for param in &procedure.definition.parameters {
         match sizeof_type_values(
            &param.p_type.e_type,
            generation_context.enum_info,
            generation_context.struct_size_info,
         )
         .cmp(&1)
         {
            std::cmp::Ordering::Less => (),
            std::cmp::Ordering::Equal => {
               get_stack_address_of_local(param.var_id, &mut generation_context);
               generation_context
                  .active_fcn
                  .instruction(&Instruction::LocalGet(values_index));
               simple_store(&param.p_type.e_type, &mut generation_context);
               values_index += 1;
            }
            std::cmp::Ordering::Greater => {
               get_stack_address_of_local(param.var_id, &mut generation_context);
               generation_context
                  .active_fcn
                  .instruction(&Instruction::GlobalSet(MEM_ADDRESS));
               dynamic_move_locals_of_type_to_dest(
                  &Instruction::GlobalGet(MEM_ADDRESS),
                  &mut 0,
                  &mut values_index,
                  &param.p_type.e_type,
                  &mut generation_context,
               );
            }
         }
      }

      for statement in &procedure.block.statements {
         emit_statement(statement, &mut generation_context, interner);
      }

      if procedure.block.statements.last().map_or(false, |x| {
         statement_always_returns(&x.statement, generation_context.expressions)
      }) {
         // No need to adjust stack; it was done in the return statement
         if !matches!(
            procedure.block.statements.last().unwrap().statement,
            Statement::Return(_)
         ) {
            // Roland can be smarter than WASM permits, hence we make this explicit to avoid tripping stack violations
            generation_context.active_fcn.instruction(&Instruction::Unreachable);
         }
      } else {
         adjust_stack_function_exit(&mut generation_context);
      }

      generation_context.out.close();
   }

   let mut needed_store_fns = IndexSet::new();
   std::mem::swap(&mut needed_store_fns, &mut generation_context.needed_store_fns);
   for (i, e_type) in needed_store_fns.iter().enumerate() {
      generation_context
         .out
         .emit_store_function_start(i, e_type, generation_context.struct_info);
      dynamic_move_locals_of_type_to_dest(
         &Instruction::LocalGet(0),
         &mut 0,
         &mut 1,
         e_type,
         &mut generation_context,
      );
      generation_context.out.close();
   }

   let (table_section, element_section) = {
      let mut table = TableSection::new();

      let table_type = TableType {
         element_type: RefType::FUNCREF,
         minimum: generation_context.procedure_to_table_index.len() as u32,
         maximum: Some(generation_context.procedure_to_table_index.len() as u32),
      };

      table.table(table_type);

      let mut elem = ElementSection::new();
      elem.active(Some(0), &ConstExpr::i32_const(0), RefType::FUNCREF, todo!());

      (table, elem)
   };

   for indirect_callee_id in generation_context.indirect_callees.iter() {
      let pp_type = generation_context.expressions[*indirect_callee_id]
         .exp_type
         .as_ref()
         .unwrap();
      match pp_type {
         ExpressionType::ProcedurePointer { parameters, ret_type } => {
            generation_context.out.emit_function_type(
               *indirect_callee_id,
               parameters.iter(),
               ret_type,
               generation_context.struct_info,
            );
         }
         _ => unreachable!(),
      }
   }

   let mut module = Module::new();
   module.section(&type_section);
   module.section(&import_section);
   // function section
   module.section(&table_section);
   module.section(&memory_section);
   module.section(&global_section);
   module.section(&export_section);
   // start section
   module.section(&element_section);
   // datacount section
   // code section
   // data section

   module.finish()
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
      Statement::VariableDeclaration(_, opt_en, _, var_id) => {
         if let Some(en) = opt_en {
            get_stack_address_of_local(*var_id, generation_context);
            do_emit_and_load_lval(*en, generation_context, interner);
            let val_type = generation_context.expressions[*en].exp_type.as_ref().unwrap();
            store(val_type, generation_context, interner);
         }
      }
      Statement::Block(bn) => {
         for statement in &bn.statements {
            emit_statement(statement, generation_context, interner);
         }
      }
      Statement::For(_, start, end, bn, inclusive, start_var_id) => {
         let start_expr = &generation_context.expressions[*start];

         let (wasm_type, suffix) = match start_expr.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => int_to_wasm_runtime_and_suffix(*x),
            _ => unreachable!(),
         };

         debug_assert!(!*inclusive); // unimplemented

         generation_context.active_fcn.instruction(&Instruction::Block(BlockType::Empty)); // b
         generation_context.active_fcn.instruction(&Instruction::Loop(BlockType::Empty));
         generation_context.active_fcn.instruction(&Instruction::Block(BlockType::Empty)); // bi
         // Check and break if needed
         {
            get_stack_address_of_local(*start_var_id, generation_context);
            load(start_expr.exp_type.as_ref().unwrap(), generation_context);
            do_emit_and_load_lval(*end, generation_context, interner);
            writeln!(generation_context.out.out, "{}.ge{}", wasm_type, suffix).unwrap();

            generation_context.active_fcn.instruction(&Instruction::If(BlockType::Empty));
            // then
            generation_context.active_fcn.instruction(&Instruction::Br(2));
            // finish if
            generation_context.active_fcn.instruction(&Instruction::End);
         }
         for statement in &bn.statements {
            emit_statement(statement, generation_context, interner);
         }
         generation_context.active_fcn.instruction(&Instruction::End); // end block bi

         // Increment
         {
            get_stack_address_of_local(*start_var_id, generation_context);
            get_stack_address_of_local(*start_var_id, generation_context);
            load(start_expr.exp_type.as_ref().unwrap(), generation_context);
            writeln!(generation_context.out.out, "{}.const 1", wasm_type).unwrap();
            writeln!(generation_context.out.out, "{}.add", wasm_type).unwrap();
            store(start_expr.exp_type.as_ref().unwrap(), generation_context, interner);
         }
         generation_context.active_fcn.instruction(&Instruction::Br(0));
         generation_context.active_fcn.instruction(&Instruction::End);
         generation_context.active_fcn.instruction(&Instruction::End);
      }
      Statement::Loop(bn) => {
         //generation_context.active_fcn.blo
         // nocheckin does it really have to be this complicated? seems like the innermost block is not necessary?
         generation_context.active_fcn.instruction(&Instruction::Block(BlockType::Empty));
         generation_context.active_fcn.instruction(&Instruction::Loop(BlockType::Empty));
         generation_context.active_fcn.instruction(&Instruction::Block(BlockType::Empty));
         for statement in &bn.statements {
            emit_statement(statement, generation_context, interner);
         }
         generation_context.active_fcn.instruction(&Instruction::End); // end block bi
         generation_context.active_fcn.instruction(&Instruction::Br(0));
         generation_context.active_fcn.instruction(&Instruction::End); // end loop
         generation_context.active_fcn.instruction(&Instruction::End); // end block b
      }
      Statement::Break => {
         generation_context.active_fcn.instruction(&Instruction::Br(2));
      }
      Statement::Continue => {
         generation_context.active_fcn.instruction(&Instruction::Br(0));
      }
      Statement::Expression(en) => {
         do_emit(*en, generation_context, interner);
         for _ in 0..sizeof_type_values(
            generation_context.expressions[*en].exp_type.as_ref().unwrap(),
            generation_context.enum_info,
            generation_context.struct_size_info,
         ) {
            generation_context.active_fcn.instruction(&Instruction::Drop);
         }
      }
      Statement::IfElse(en, block_1, block_2) => {
         do_emit_and_load_lval(*en, generation_context, interner);
         generation_context.active_fcn.instruction(&Instruction::If(BlockType::Empty));
         // then
         for statement in &block_1.statements {
            emit_statement(statement, generation_context, interner);
         }
         // else
         generation_context.active_fcn.instruction(&Instruction::Else);
         emit_statement(block_2, generation_context, interner);
         // finish if
         generation_context.active_fcn.instruction(&Instruction::End);
      }
      Statement::Return(en) => {
         do_emit_and_load_lval(*en, generation_context, interner);

         if generation_context.expressions[*en]
            .exp_type
            .as_ref()
            .unwrap()
            .is_never()
         {
            // WASM has strict rules about the stack - we need a literal "unreachable" to bypass them
            generation_context.active_fcn.instruction(&Instruction::Unreachable);
         } else {
            adjust_stack_function_exit(generation_context);
            generation_context.active_fcn.instruction(&Instruction::Return);
         }
      }
   }
}

fn do_emit_and_load_lval(
   expr_index: ExpressionId,
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

fn emit_literal_bytes(buf: &mut Vec<u8>, expr_index: ExpressionId, generation_context: &mut GenerationContext) {
   let expr_node = &generation_context.expressions[expr_index];
   match &expr_node.expression {
      Expression::BoundFcnLiteral(proc_name, _) => {
         let (my_index, _) = generation_context.procedure_to_table_index.insert_full(proc_name.str);
         // todo: truncation
         buf.extend((my_index as u32).to_le_bytes());
      }
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(x) => {
         buf.extend(u8::from(*x).to_le_bytes());
      }
      Expression::EnumLiteral(_, _) => unreachable!(),
      Expression::IntLiteral { val: x, .. } => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => x.width,
            ExpressionType::Pointer(_) => IntWidth::Pointer,
            _ => unreachable!(),
         }
         .as_num_bytes();
         for w in 0..width {
            let val = (x >> (8 * w)) & 0xff;
            buf.push(val as u8);
         }
      }
      Expression::FloatLiteral(x) => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Float(x) => x.width,
            _ => unreachable!(),
         };
         match width {
            FloatWidth::Eight => {
               buf.extend(x.to_bits().to_le_bytes());
            }
            FloatWidth::Four => {
               buf.extend((*x as f32).to_bits().to_le_bytes());
            }
         }
      }
      Expression::StringLiteral(str) => {
         let (offset, len) = generation_context.literal_offsets.get(str).unwrap();
         buf.extend(offset.to_le_bytes());
         buf.extend(len.to_le_bytes());
      }
      Expression::StructLiteral(s_name, fields) => {
         // We need to emit this in the proper order!!
         let map: HashMap<StrId, ExpressionId> = fields.iter().map(|x| (x.0, x.1)).collect();
         let si = generation_context.struct_info.get(&s_name.str).unwrap();
         let ssi = generation_context.struct_size_info.get(&s_name.str).unwrap();
         for (field, next_field) in si.field_types.iter().zip(si.field_types.keys().skip(1)) {
            let value_of_field = map.get(field.0).copied().unwrap();
            emit_literal_bytes(buf, value_of_field, generation_context);
            let this_offset = ssi.field_offsets.get(field.0).unwrap();
            let next_offset = ssi.field_offsets.get(next_field).unwrap();
            let padding_bytes = next_offset
               - this_offset
               - sizeof_type_mem(
                  &field.1.e_type,
                  generation_context.enum_info,
                  generation_context.struct_size_info,
               );
            for _ in 0..padding_bytes {
               buf.push(0);
            }
         }
         if let Some(last_field) = si.field_types.iter().last() {
            let value_of_field = map.get(last_field.0).copied().unwrap();
            emit_literal_bytes(buf, value_of_field, generation_context);
            let this_offset = ssi.field_offsets.get(last_field.0).unwrap();
            let next_offset = ssi.mem_size;
            let padding_bytes = next_offset
               - this_offset
               - sizeof_type_mem(
                  &last_field.1.e_type,
                  generation_context.enum_info,
                  generation_context.struct_size_info,
               );
            for _ in 0..padding_bytes {
               buf.push(0);
            }
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            emit_literal_bytes(buf, *expr, generation_context);
         }
      }
      _ => unreachable!(),
   }
}

fn do_emit(expr_index: ExpressionId, generation_context: &mut GenerationContext, interner: &mut Interner) {
   let expr_node = &generation_context.expressions[expr_index];
   match &expr_node.expression {
      Expression::UnitLiteral => (),
      Expression::BoundFcnLiteral(proc_name, _bound_type_params) => {
         if let ExpressionType::ProcedurePointer { .. } = expr_node.exp_type.as_ref().unwrap() {
            emit_procedure_pointer_index(proc_name.str, generation_context);
         }
      }
      Expression::BoolLiteral(x) => {
         generation_context
            .active_fcn
            .instruction(&Instruction::I32Const(i32::from(*x)));
      }
      Expression::EnumLiteral(_, _) => unreachable!(),
      Expression::IntLiteral { val: x, .. } => {
         let (signed, wasm_type) = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => match x.width {
               IntWidth::Eight => (x.signed, WasmType::Int64),
               _ => (x.signed, WasmType::Int32),
            },
            // can occur when an int->ptr transmute is constant folded
            ExpressionType::Pointer(_) => (false, WasmType::Int32),
            _ => unreachable!(),
         };
         if signed {
            writeln!(generation_context.out.out, "{}.const {}", wasm_type, *x as i64).unwrap();
         } else {
            writeln!(generation_context.out.out, "{}.const {}", wasm_type, *x).unwrap();
         }
      }
      Expression::FloatLiteral(x) => {
         let wasm_type = type_to_wasm_type_basic(expr_node.exp_type.as_ref().unwrap());
         if x.is_nan() {
            // It would be nice to support NaN payloads too, but it was kind of a pain when I tried.
            // Better maybe would be to just output everything as a hex float?
            // This would all be so much better if the web assembly text format had a
            // "raw:0x{hex}" format. I don't agree with their reasoning not to support it.
            if x.is_sign_negative() {
               writeln!(generation_context.out.out, "{}.const -nan", wasm_type).unwrap();
            } else {
               writeln!(generation_context.out.out, "{}.const nan", wasm_type).unwrap();
            }
         } else {
            writeln!(generation_context.out.out, "{}.const {}", wasm_type, x).unwrap();
         }
      }
      Expression::StringLiteral(str) => {
         let (offset, len) = generation_context.literal_offsets.get(str).unwrap();
         generation_context
            .active_fcn
            .instruction(&Instruction::I32Const(*offset as i32));
         generation_context
            .active_fcn
            .instruction(&Instruction::I32Const(*len as i32));
      }
      Expression::BinaryOperator {
         operator: BinOp::LogicalAnd,
         lhs,
         rhs,
      } => {
         do_emit_and_load_lval(*lhs, generation_context, interner);
         generation_context
            .out
            .emit_if_start(&ExpressionType::Bool, generation_context.struct_info);
         // then
         generation_context.out.emit_then_start();
         do_emit_and_load_lval(*rhs, generation_context, interner);
         generation_context.out.close();
         // else
         generation_context.out.emit_else_start();
         generation_context.active_fcn.instruction(&Instruction::I32Const(0));
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
         generation_context
            .out
            .emit_if_start(&ExpressionType::Bool, generation_context.struct_info);
         // then
         generation_context.out.emit_then_start();
         generation_context.active_fcn.instruction(&Instruction::I32Const(1));
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
            ExpressionType::Int(x) => int_to_wasm_runtime_and_suffix(*x),
            ExpressionType::Enum(_) => unreachable!(),
            ExpressionType::Float(x) => match x.width {
               FloatWidth::Eight => (WasmType::Float64, ""),
               FloatWidth::Four => (WasmType::Float32, ""),
            },
            ExpressionType::Bool => (WasmType::Int32, "_u"),
            _ => unreachable!(),
         };
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
         let e = &generation_context.expressions[*e_index];

         if let ExpressionType::ProcedureItem(proc_name, _bound_type_params) = e.exp_type.as_ref().unwrap() {
            emit_procedure_pointer_index(*proc_name, generation_context);
            return;
         }

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
               let wasm_type = type_to_wasm_type_basic(expr_node.exp_type.as_ref().unwrap());
               do_emit_and_load_lval(*e_index, generation_context, interner);

               if *e.exp_type.as_ref().unwrap() == ExpressionType::Bool {
                  writeln!(generation_context.out.out, "{}.eqz", wasm_type).unwrap();
               } else {
                  complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
               }
            }
            UnOp::Negate => {
               let wasm_type = type_to_wasm_type_basic(expr_node.exp_type.as_ref().unwrap());
               do_emit_and_load_lval(*e_index, generation_context, interner);

               match expr_node.exp_type.as_ref().unwrap() {
                  ExpressionType::Int(_) | ExpressionType::Bool => {
                     complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
                     writeln!(generation_context.out.out, "{}.const 1", wasm_type).unwrap();
                     writeln!(generation_context.out.out, "{}.add", wasm_type).unwrap();
                  }
                  ExpressionType::Float(_) => {
                     writeln!(generation_context.out.out, "{}.neg", wasm_type).unwrap();
                  }
                  _ => unreachable!(),
               }
            }
         }
      }
      Expression::Cast {
         cast_type: CastType::Extend,
         target_type,
         expr: e,
      } => {
         do_emit_and_load_lval(*e, generation_context, interner);

         let e = &generation_context.expressions[*e];

         let (source_width, source_is_signed) = match e.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => (x.width, x.signed),
            ExpressionType::Bool => (IntWidth::One, false),
            _ => unreachable!(),
         };

         let suffix = if source_is_signed { "s" } else { "u" };

         match target_type {
            ExpressionType::Int(x) if x.width == IntWidth::Eight && source_width.as_num_bytes() <= 4 => {
               writeln!(generation_context.out.out, "i64.extend_i32_{}", suffix).unwrap();
            }
            ExpressionType::Int(_) => {
               // nop
            }
            ExpressionType::Float(_) => {
               generation_context.active_fcn.instruction(&Instruction::F64PromoteF32);
            }
            _ => unreachable!(),
         }
      }
      Expression::Cast {
         cast_type: CastType::Transmute,
         target_type,
         expr: e_id,
      } => {
         let e = &generation_context.expressions[*e_id];

         if e.expression.is_lvalue_disregard_consts(generation_context.expressions) {
            do_emit(*e_id, generation_context, interner);
            load(target_type, generation_context);
         } else {
            debug_assert!(is_wasm_compatible_rval_transmute(
               e.exp_type.as_ref().unwrap(),
               target_type
            ));
            do_emit(*e_id, generation_context, interner);

            if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Float(_))
               && matches!(target_type, ExpressionType::Int(_) | ExpressionType::Pointer(_))
            {
               // float -> int
               match target_type {
                  ExpressionType::Pointer(_) => {
                     // @FixedPointerWidth
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I32ReinterpretF32);
                  }
                  ExpressionType::Int(x) if x.width.as_num_bytes() == 4 => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I32ReinterpretF32);
                  }
                  ExpressionType::Int(x) if x.width.as_num_bytes() == 8 => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I64ReinterpretF64);
                  }
                  _ => unreachable!(),
               }
            } else if matches!(
               e.exp_type.as_ref().unwrap(),
               ExpressionType::Int(_) | ExpressionType::Pointer(_)
            ) && matches!(target_type, ExpressionType::Float(_))
            {
               // int -> float
               match *target_type {
                  F32_TYPE => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::F32ReinterpretI32);
                  }
                  F64_TYPE => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::F64ReinterpretI64);
                  }
                  _ => unreachable!(),
               }
            }
         }
      }
      Expression::Cast {
         cast_type: CastType::Truncate,
         target_type,
         expr: e,
      } => {
         do_emit_and_load_lval(*e, generation_context, interner);

         let e = &generation_context.expressions[*e];

         if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Int(_))
            && matches!(target_type, ExpressionType::Int(_))
         {
            // 8bytes -> (4, 2, 1) bytes is a wrap
            // anything else is a nop

            if sizeof_type_wasm(
               e.exp_type.as_ref().unwrap(),
               generation_context.enum_info,
               generation_context.struct_size_info,
            ) > 4
               && sizeof_type_wasm(
                  target_type,
                  generation_context.enum_info,
                  generation_context.struct_size_info,
               ) <= 4
            {
               generation_context.active_fcn.instruction(&Instruction::I32WrapI64);
            }
         } else if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Float(_))
            && matches!(target_type, ExpressionType::Int(_))
         {
            // float -> int
            // i32.trunc_f32_s
            let (target_type_str, suffix) = match target_type {
               ExpressionType::Int(x) => {
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
            let dest_type = type_to_wasm_type_basic(e.exp_type.as_ref().unwrap());
            writeln!(
               generation_context.out.out,
               "{}.trunc_sat_{}{}",
               target_type_str, dest_type, suffix
            )
            .unwrap();
         } else if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Int(_))
            && matches!(target_type, ExpressionType::Float(_))
         {
            // int -> float
            let target_type_str = type_to_wasm_type_basic(target_type);

            let (dest_type_str, suffix) = match e.exp_type.as_ref().unwrap() {
               ExpressionType::Int(x) => {
                  let base_str = match x.width {
                     IntWidth::Eight => "i64",
                     IntWidth::Pointer => "i32",
                     IntWidth::Four => "i32",
                     IntWidth::Two => "i32",
                     IntWidth::One => "i32",
                  };
                  (base_str, if x.signed { "_s" } else { "_u" })
               }
               _ => unreachable!(),
            };
            writeln!(
               generation_context.out.out,
               "{}.convert_{}{}",
               target_type_str, dest_type_str, suffix
            )
            .unwrap();
         } else if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Float(_))
            && matches!(target_type, ExpressionType::Float(_))
         {
            // f64 -> f32
            generation_context.active_fcn.instruction(&Instruction::F32DemoteF64);
         }
      }
      Expression::Variable(id) => {
         if let Some(v) = generation_context.static_addresses.get(id).copied() {
            generation_context
               .active_fcn
               .instruction(&Instruction::I32Const(v as i32));
         } else {
            get_stack_address_of_local(*id, generation_context);
         }
      }
      Expression::UnresolvedVariable(_) => {
         unreachable!()
      }
      Expression::ProcedureCall { proc_expr, args } => {
         if !matches!(
            generation_context.expressions[*proc_expr].exp_type,
            Some(ExpressionType::ProcedurePointer { .. })
         ) {
            // shouldn't place anything on the stack
            do_emit_and_load_lval(*proc_expr, generation_context, interner);
         }

         // Output the non-named parameters
         let mut first_named_arg = None;
         for (i, arg) in args.iter().enumerate() {
            if arg.name.is_some() {
               first_named_arg = Some(i);
               break;
            }

            do_emit_and_load_lval(arg.expr, generation_context, interner);
         }

         if let Some(i) = first_named_arg {
            let mut named_args = vec![];
            named_args.extend_from_slice(&args[i..]);

            // Output each named parameter in canonical order
            named_args.sort_unstable_by_key(|x| x.name);
            for named_arg in named_args {
               do_emit_and_load_lval(named_arg.expr, generation_context, interner);
            }
         }

         match generation_context.expressions[*proc_expr].exp_type.as_ref().unwrap() {
            ExpressionType::ProcedureItem(proc_name, _) => {
               generation_context.out.emit_call(*proc_name, interner);
            }
            ExpressionType::ProcedurePointer { .. } => {
               do_emit_and_load_lval(*proc_expr, generation_context, interner);
               writeln!(generation_context.out.out, "call_indirect 0 (type $::{})", proc_expr.0).unwrap();
               generation_context.indirect_callees.push(*proc_expr);
            }
            _ => unreachable!(),
         };
      }
      Expression::StructLiteral(s_name, fields) => {
         let map: HashMap<StrId, ExpressionId> = fields.iter().map(|x| (x.0, x.1)).collect();
         let si = generation_context.struct_info.get(&s_name.str).unwrap();
         for field in si.field_types.iter() {
            if let Some(value_of_field) = map.get(field.0).copied() {
               do_emit_and_load_lval(value_of_field, generation_context, interner);
            } else {
               // Must be a default value
               let default_value = si.default_values.get(field.0).copied().unwrap();
               do_emit(default_value, generation_context, interner);
            }
         }
      }
      Expression::FieldAccess(field_names, lhs_id) => {
         fn calculate_offset(
            lhs_type: &ExpressionType,
            field_names: &[StrId],
            generation_context: &mut GenerationContext,
         ) {
            let ExpressionType::Struct(mut struct_name) = lhs_type else { unreachable!() };
            let mut mem_offset = 0;

            for field_name in field_names.iter().take(field_names.len() - 1) {
               mem_offset += generation_context
                  .struct_size_info
                  .get(&struct_name)
                  .unwrap()
                  .field_offsets
                  .get(field_name)
                  .unwrap();
               struct_name = match generation_context
                  .struct_info
                  .get(&struct_name)
                  .unwrap()
                  .field_types
                  .get(field_name)
                  .map(|x| &x.e_type)
               {
                  Some(ExpressionType::Struct(x)) => *x,
                  _ => unreachable!(),
               };
            }

            let last_field_name = field_names.last().unwrap();
            mem_offset += generation_context
               .struct_size_info
               .get(&struct_name)
               .unwrap()
               .field_offsets
               .get(last_field_name)
               .unwrap();

            generation_context.emit_const_add_i32(mem_offset);
         }

         let lhs = &generation_context.expressions[*lhs_id];

         debug_assert!(lhs
            .expression
            .is_lvalue_disregard_consts(generation_context.expressions));

         do_emit(*lhs_id, generation_context, interner);
         calculate_offset(lhs.exp_type.as_ref().unwrap(), field_names, generation_context);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            do_emit_and_load_lval(*expr, generation_context, interner);
         }
      }
      Expression::ArrayIndex { array, index } => {
         fn calculate_offset(
            array: ExpressionId,
            index_e: ExpressionId,
            generation_context: &mut GenerationContext,
            interner: &mut Interner,
         ) {
            let sizeof_inner = match &generation_context.expressions[array].exp_type {
               Some(ExpressionType::Array(x, _)) => {
                  sizeof_type_mem(x, generation_context.enum_info, generation_context.struct_size_info)
               }
               _ => unreachable!(),
            };

            if let Expression::IntLiteral { val: x, .. } = generation_context.expressions[index_e].expression {
               // Safe assert due to inference and constant folding validating this
               let val_32 = u32::try_from(x).unwrap();
               let result = sizeof_inner.wrapping_mul(val_32);
               generation_context.emit_const_add_i32(result);
            } else {
               do_emit_and_load_lval(index_e, generation_context, interner);
               generation_context.emit_const_mul_i32(sizeof_inner);
               generation_context.active_fcn.instruction(&Instruction::I32Add);
            }
         }

         debug_assert!(generation_context.expressions[*array]
            .expression
            .is_lvalue_disregard_consts(generation_context.expressions));

         do_emit(*array, generation_context, interner);
         calculate_offset(*array, *index, generation_context, interner);
      }
   }
}

fn complement_val(t_type: &ExpressionType, wasm_type: WasmType, generation_context: &mut GenerationContext) {
   let magic_const: u64 = match *t_type {
      crate::type_data::U8_TYPE => u64::from(std::u8::MAX),
      crate::type_data::U16_TYPE => u64::from(std::u16::MAX),
      crate::type_data::U32_TYPE => u64::from(std::u32::MAX),
      // @FixedPointerWidth
      crate::type_data::USIZE_TYPE => u64::from(std::u32::MAX),
      crate::type_data::U64_TYPE => std::u64::MAX,
      crate::type_data::I8_TYPE => u64::from(std::u32::MAX),
      crate::type_data::I16_TYPE => u64::from(std::u32::MAX),
      crate::type_data::I32_TYPE => u64::from(std::u32::MAX),
      // @FixedPointerWidth
      crate::type_data::ISIZE_TYPE => u64::from(std::u32::MAX),
      crate::type_data::I64_TYPE => std::u64::MAX,
      _ => unreachable!(),
   };
   writeln!(generation_context.out.out, "{}.const {}", wasm_type, magic_const).unwrap();
   writeln!(generation_context.out.out, "{}.xor", wasm_type).unwrap();
}

/// Places the address of given local on the stack
fn get_stack_address_of_local(id: VariableId, generation_context: &mut GenerationContext) {
   let offset = generation_context.local_offsets_mem.get(&id).copied().unwrap();
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalGet(BP));
   generation_context.emit_const_add_i32(offset);
}

fn load(val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   if sizeof_type_values(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) > 1
   {
      generation_context
         .active_fcn
         .instruction(&Instruction::GlobalSet(MEM_ADDRESS));
      complex_load(0, val_type, generation_context);
   } else {
      simple_load(val_type, generation_context);
   }
}

fn complex_load(mut offset: u32, val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   match val_type {
      ExpressionType::Struct(x) => {
         for (field_name, field) in generation_context.struct_info.get(x).unwrap().field_types.iter() {
            let field_offset = generation_context
               .struct_size_info
               .get(x)
               .unwrap()
               .field_offsets
               .get(field_name)
               .unwrap();
            match sizeof_type_values(
               &field.e_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            )
            .cmp(&1)
            {
               std::cmp::Ordering::Less => (),
               std::cmp::Ordering::Equal => {
                  generation_context
                     .active_fcn
                     .instruction(&Instruction::GlobalGet(MEM_ADDRESS));
                  generation_context.emit_const_add_i32(offset + field_offset);
                  simple_load(&field.e_type, generation_context);
               }
               std::cmp::Ordering::Greater => complex_load(offset + field_offset, &field.e_type, generation_context),
            }
         }
      }
      ExpressionType::Array(a_type, len) => {
         for _ in 0..*len {
            match sizeof_type_values(
               a_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            )
            .cmp(&1)
            {
               std::cmp::Ordering::Less => (),
               std::cmp::Ordering::Equal => {
                  generation_context
                     .active_fcn
                     .instruction(&Instruction::GlobalGet(MEM_ADDRESS));
                  generation_context.emit_const_add_i32(offset);
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
   // If this is a tiny struct or array, drill into the inner type
   match val_type {
      ExpressionType::Struct(x) => {
         let si = generation_context.struct_info.get(x).unwrap();
         // Find the first non-zero-sized struct field and load that
         // (there should only be one if we're in simple_load)
         for (_, field_type_node) in si.field_types.iter() {
            let field_type = &field_type_node.e_type;
            match sizeof_type_values(
               field_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            ) {
               0 => continue,
               1 => return simple_load(field_type, generation_context),
               _ => unreachable!(),
            }
         }
      }
      ExpressionType::Array(inner_type, _len) => {
         return simple_load(inner_type, generation_context);
      }
      _ => (),
   }
   if sizeof_type_values(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) == 0
   {
      // Drop the load address; nothing to load
      generation_context.active_fcn.instruction(&Instruction::Drop);
   } else if sizeof_type_mem(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) == sizeof_type_wasm(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) {
      writeln!(generation_context.out.out, "{}.load", type_to_wasm_type_basic(val_type)).unwrap();
   } else {
      let (load_suffx, sign_suffix) = match val_type {
         ExpressionType::Int(x) => {
            let load_suffx = match x.width {
               IntWidth::Eight => "64",
               IntWidth::Four | IntWidth::Pointer => "32",
               IntWidth::Two => "16",
               IntWidth::One => "8",
            };
            let sign_suffix = if x.signed { "_s" } else { "_u" };
            (load_suffx, sign_suffix)
         }
         ExpressionType::Enum(_) => unreachable!(),
         ExpressionType::Float(_) => ("", ""),
         ExpressionType::Bool => ("8", "_u"),
         _ => unreachable!(),
      };
      writeln!(
         generation_context.out.out,
         "{}.load{}{}",
         type_to_wasm_type_basic(val_type),
         load_suffx,
         sign_suffix
      )
      .unwrap();
   }
}

fn store(val_type: &ExpressionType, generation_context: &mut GenerationContext, interner: &mut Interner) {
   if sizeof_type_values(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) == 0
   {
      // drop the placement address
      generation_context.active_fcn.instruction(&Instruction::Drop);
   } else if sizeof_type_values(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) == 1
   {
      simple_store(val_type, generation_context);
   } else if sizeof_type_values(
      val_type,
      generation_context.enum_info,
      generation_context.struct_size_info,
   ) > 1
   {
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
      ExpressionType::Struct(x) => {
         let si = generation_context.struct_info.get(x).unwrap();
         // Find the first non-zero-sized struct field and store that
         // (there should only be one if we're in simple_store)
         for (_, field_type_node) in si.field_types.iter() {
            let field_type = &field_type_node.e_type;
            match sizeof_type_values(
               field_type,
               generation_context.enum_info,
               generation_context.struct_size_info,
            ) {
               0 => continue,
               1 => return simple_store(field_type, generation_context),
               _ => unreachable!(),
            }
         }
      }
      ExpressionType::Array(inner_type, _len) => {
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
      generation_context
         .active_fcn
         .instruction(&type_to_wasm_type_basic(val_type).store_instruction());
   } else {
      let load_suffx = match val_type {
         ExpressionType::Int(x) => match x.width {
            IntWidth::Eight => "64",
            IntWidth::Four | IntWidth::Pointer => "32",
            IntWidth::Two => "16",
            IntWidth::One => "8",
         },
         ExpressionType::Enum(_) => unreachable!(),
         ExpressionType::Float(_) => "",
         ExpressionType::Bool => "8",
         _ => unreachable!(),
      };
      writeln!(
         generation_context.out.out,
         "{}.store{}",
         type_to_wasm_type_basic(val_type),
         load_suffx,
      )
      .unwrap();
   }
}

fn adjust_stack_function_entry(generation_context: &mut GenerationContext) {
   if generation_context.sum_sizeof_locals_mem == MINIMUM_STACK_FRAME_SIZE {
      return;
   }

   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalGet(SP));
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalGet(BP));
   generation_context
      .active_fcn
      .instruction(&Instruction::I32Store(null_mem_arg()));
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalGet(SP));
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalSet(BP));
   adjust_stack(generation_context, &Instruction::I32Add);
}

fn adjust_stack_function_exit(generation_context: &mut GenerationContext) {
   if generation_context.sum_sizeof_locals_mem == MINIMUM_STACK_FRAME_SIZE {
      return;
   }

   adjust_stack(generation_context, &Instruction::I32Sub);
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalGet(SP));
   generation_context
      .active_fcn
      .instruction(&Instruction::I32Load(null_mem_arg()));
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalSet(BP));
}

fn adjust_stack(generation_context: &mut GenerationContext, instr: &Instruction) {
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalGet(SP));
   // ensure that each stack frame is strictly aligned so that internal stack frame alignment is preserved
   let adjust_value = aligned_address(generation_context.sum_sizeof_locals_mem, 8);
   generation_context
      .active_fcn
      .instruction(&Instruction::I32Const(adjust_value as i32));
   generation_context.active_fcn.instruction(instr);
   generation_context
      .active_fcn
      .instruction(&Instruction::GlobalSet(SP));
}

fn emit_procedure_pointer_index(proc_name: StrId, generation_context: &mut GenerationContext) {
   let (my_index, _) = generation_context.procedure_to_table_index.insert_full(proc_name);
   generation_context
      .active_fcn
      .instruction(&Instruction::I32Const(my_index as u32 as i32));
}

fn null_mem_arg() -> MemArg {
   MemArg {
      offset: 0,
      align: 0,
      memory_index: 0,
   }
}
