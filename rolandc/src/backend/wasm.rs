use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};
use wasm_encoder::{
   BlockType, CodeSection, ConstExpr, DataSection, ElementSection, Elements, EntityType, ExportSection, Function,
   FunctionSection, GlobalSection, GlobalType, ImportSection, Instruction, MemArg, MemorySection, MemoryType, Module,
   NameMap, NameSection, RefType, TableSection, TableType, TypeSection, ValType,
};

use super::linearize::{post_order, Cfg, CfgInstruction, CFG_END_NODE};
use super::regalloc::{RegallocResult, VarSlot};
use crate::dominators::{compute_dominators, DominatorTree};
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, BinOp, CastType, Expression, ExpressionId, ProcImplSource, ProcedureDefinition, ProcedureId, Program, UnOp,
   UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::{GlobalInfo, StorageKind};
use crate::size_info::{aligned_address, mem_alignment, sizeof_type_mem, sizeof_type_values, sizeof_type_wasm};
use crate::type_data::{ExpressionType, FloatType, FloatWidth, IntType, IntWidth, F32_TYPE, F64_TYPE};
use crate::{CompilationConfig, Target};

// globals
const SP: u32 = 0;

#[derive(Clone, Copy, Debug)]
enum ContainingSyntax {
   IfThenElse,
   LoopHeadedBy(usize),
   BlockFollowedBy(usize),
}

struct GenerationContext<'a> {
   active_fcn: wasm_encoder::Function,
   type_manager: TypeManager<'a>,
   literal_offsets: HashMap<StrId, (u32, u32)>,
   global_info: &'a IndexMap<VariableId, GlobalInfo>,
   static_addresses: HashMap<VariableId, u32>,
   stack_offsets_mem: HashMap<usize, u32>,
   user_defined_types: &'a UserDefinedTypeInfo,
   sum_sizeof_locals_mem: u32,
   ast: &'a AstPool,
   proc_name_table: &'a HashMap<StrId, ProcedureId>,
   procedure_to_table_index: IndexSet<ProcedureId>,
   procedure_indices: IndexSet<ProcedureId>,
   frames: Vec<ContainingSyntax>,
   var_to_slot: IndexMap<VariableId, VarSlot>,
   target: Target,
   cfg_index_to_rpo_index: HashMap<usize, usize>,
}

impl GenerationContext<'_> {
   fn emit_const_add_i32(&mut self, value: u32) {
      if value > 0 {
         self.active_fcn.instruction(&Instruction::I32Const(value as i32));
         self.active_fcn.instruction(&Instruction::I32Add);
      }
   }

   fn emit_const_sub_i32(&mut self, value: u32) {
      if value > 0 {
         self.active_fcn.instruction(&Instruction::I32Const(value as i32));
         self.active_fcn.instruction(&Instruction::I32Sub);
      }
   }

   fn emit_const_mul_i32(&mut self, value: u32) {
      if value != 1 {
         self.active_fcn.instruction(&Instruction::I32Const(value as i32));
         self.active_fcn.instruction(&Instruction::I32Mul);
      }
   }
}

fn type_to_wasm_type(t: &ExpressionType, udt: &UserDefinedTypeInfo, target: Target, buf: &mut Vec<ValType>) {
   if sizeof_type_mem(t, udt, target) == 0 {
      return;
   }

   match t {
      ExpressionType::Union(_, _) | ExpressionType::Struct(_, _) | ExpressionType::Array(_, _) => {
         buf.push(ValType::I32);
      }
      _ => buf.push(type_to_wasm_type_basic(t)),
   }
}

fn type_to_wasm_type_basic(t: &ExpressionType) -> ValType {
   match t {
      ExpressionType::Int(x) => match x.width {
         IntWidth::Eight => ValType::I64,
         _ => ValType::I32,
      },
      ExpressionType::Float(x) => match x.width {
         FloatWidth::Eight => ValType::F64,
         FloatWidth::Four => ValType::F32,
      },
      ExpressionType::Pointer(_) | ExpressionType::ProcedurePointer { .. } | ExpressionType::Bool => ValType::I32,
      _ => unreachable!(),
   }
}

#[derive(Hash, Eq, PartialEq)]
struct FunctionValTypes {
   param_val_types: Vec<ValType>,
   ret_val_types: Vec<ValType>,
}

impl FunctionValTypes {
   fn new() -> Self {
      FunctionValTypes {
         param_val_types: vec![],
         ret_val_types: vec![],
      }
   }

   fn clear(&mut self) {
      self.param_val_types.clear();
      self.ret_val_types.clear();
   }
}

impl Default for FunctionValTypes {
   fn default() -> Self {
      FunctionValTypes::new()
   }
}

struct TypeManager<'a> {
   udt: &'a UserDefinedTypeInfo,
   target: Target,
   function_val_types: FunctionValTypes,
   registered_types: IndexSet<FunctionValTypes>,
   type_section: TypeSection,
}

impl TypeManager<'_> {
   fn new(udt: &UserDefinedTypeInfo, target: Target) -> TypeManager {
      TypeManager {
         udt,
         target,
         function_val_types: FunctionValTypes::new(),
         registered_types: IndexSet::new(),
         type_section: TypeSection::new(),
      }
   }

   fn register_or_find_type_by_definition(&mut self, def: &ProcedureDefinition) -> u32 {
      self.register_or_find_type(def.parameters.iter().map(|x| &x.p_type.e_type), &def.ret_type.e_type)
   }

   fn register_or_find_type<'a, I: IntoIterator<Item = &'a ExpressionType>>(
      &mut self,
      parameters: I,
      ret_type: &ExpressionType,
   ) -> u32 {
      self.function_val_types.clear();

      for param in parameters {
         type_to_wasm_type(
            param,
            self.udt,
            self.target,
            &mut self.function_val_types.param_val_types,
         );
      }

      type_to_wasm_type(
         ret_type,
         self.udt,
         self.target,
         &mut self.function_val_types.ret_val_types,
      );

      // (we are manually insert_full-ing here to minimize new vec allocation)
      let idx = if let Some(idx) = self.registered_types.get_index_of(&self.function_val_types) {
         idx
      } else {
         self.type_section.function(
            self.function_val_types.param_val_types.iter().copied(),
            self.function_val_types.ret_val_types.iter().copied(),
         );
         self
            .registered_types
            .insert_full(std::mem::take(&mut self.function_val_types))
            .0
      };
      idx as u32
   }
}

pub fn sort_globals(program: &mut Program, target: Target) {
   program.non_stack_var_info.sort_by(|_k_1, v_1, _k_2, v_2| {
      let e_1 = &v_1.expr_type;
      let e_2 = &v_2.expr_type;

      let alignment_1 = mem_alignment(&e_1.e_type, &program.user_defined_types, target);
      let alignment_2 = mem_alignment(&e_2.e_type, &program.user_defined_types, target);

      let sizeof_1 = sizeof_type_mem(&e_1.e_type, &program.user_defined_types, target);
      let sizeof_2 = sizeof_type_mem(&e_2.e_type, &program.user_defined_types, target);

      compare_alignment(alignment_1, sizeof_1, alignment_2, sizeof_2)
   });
}

// MEMORY LAYOUT
// 0-l literals
// l-s statics
// s+ program stack (local variables and parameters are pushed here during runtime)
pub fn emit_wasm(
   program: &mut Program,
   interner: &mut Interner,
   config: &CompilationConfig,
   mut regalloc_result: RegallocResult,
) -> Vec<u8> {
   let mut generation_context = GenerationContext {
      active_fcn: wasm_encoder::Function::new_with_locals_types([]),
      type_manager: TypeManager::new(&program.user_defined_types, config.target),
      literal_offsets: HashMap::with_capacity(program.literals.len()),
      static_addresses: HashMap::with_capacity(program.non_stack_var_info.len()),
      global_info: &program.non_stack_var_info,
      stack_offsets_mem: HashMap::new(),
      user_defined_types: &program.user_defined_types,
      sum_sizeof_locals_mem: 0,
      ast: &program.ast,
      procedure_to_table_index: IndexSet::new(),
      procedure_indices: IndexSet::new(),
      frames: Vec::new(),
      var_to_slot: regalloc_result.var_to_slot,
      proc_name_table: &program.procedure_name_table,
      target: config.target,
      cfg_index_to_rpo_index: HashMap::new(),
   };

   let mut import_section = ImportSection::new();
   let mut export_section = ExportSection::new();
   let mut function_section = FunctionSection::new();
   let mut memory_section = MemorySection::new();
   let mut data_section = DataSection::new();
   let mut code_section = CodeSection::new();

   for (id, external_procedure) in program
      .procedures
      .iter()
      .filter(|(_, v)| v.impl_source == ProcImplSource::External)
   {
      let type_index = generation_context
         .type_manager
         .register_or_find_type_by_definition(&external_procedure.definition);
      match config.target {
         Target::Qbe | Target::Lib => unreachable!(),
         Target::Wasm4 | Target::Microw8 => {
            import_section.import(
               "env",
               interner.lookup(external_procedure.definition.name.str),
               EntityType::Function(type_index),
            );
         }
         Target::Wasi => {
            import_section.import(
               "wasi_snapshot_preview1",
               interner.lookup(external_procedure.definition.name.str),
               EntityType::Function(type_index),
            );
         }
      }
      generation_context.procedure_indices.insert(id);
   }

   // Data section

   // the base memory offset varies per platform;
   // on wasm-4/microw8, we don't own all of the memory!
   let mut offset: u32 = match config.target {
      Target::Lib | Target::Qbe => unreachable!(),
      Target::Wasi => 0x0,
      Target::Wasm4 => 0x19a0,
      Target::Microw8 => 0x14000,
   };

   for s in program.literals.iter() {
      let str_value = interner.lookup(*s);
      data_section.active(
         0,
         &ConstExpr::i32_const(offset as i32),
         str_value.as_bytes().iter().copied(),
      );
      //TODO: and here truncation
      let s_len = str_value.len() as u32;
      generation_context.literal_offsets.insert(*s, (offset, s_len));
      offset += s_len;
   }

   // Handle alignment of statics
   {
      let strictest_alignment = if let Some(v) = program
         .non_stack_var_info
         .iter()
         .find(|x| !matches!(generation_context.var_to_slot.get(x.0), Some(VarSlot::Register(_))))
      {
         mem_alignment(
            &v.1.expr_type.e_type,
            generation_context.user_defined_types,
            generation_context.target,
         )
      } else {
         1
      };

      offset = aligned_address(offset, strictest_alignment);
   }
   for (static_var, static_details) in program.non_stack_var_info.iter() {
      debug_assert!(static_details.kind != StorageKind::Const);

      if generation_context.var_to_slot.contains_key(static_var) {
         continue;
      }

      generation_context.static_addresses.insert(*static_var, offset);

      offset += sizeof_type_mem(
         &static_details.expr_type.e_type,
         generation_context.user_defined_types,
         generation_context.target,
      );
   }

   let mut buf = vec![];
   for (p_var, p_static) in program.non_stack_var_info.iter().filter(|x| x.1.initializer.is_some()) {
      if generation_context.var_to_slot.contains_key(p_var) {
         continue;
      }

      literal_as_bytes(&mut buf, p_static.initializer.unwrap(), &mut generation_context);
      let static_address = generation_context.static_addresses.get(p_var).copied().unwrap();
      data_section.active(0, &ConstExpr::i32_const(static_address as i32), buf.drain(..));
   }

   // keep stack aligned
   offset = aligned_address(offset, 8);

   let (global_section, global_names) = {
      let mut globals = GlobalSection::new();
      let mut global_names = NameMap::new();
      globals.global(
         GlobalType {
            val_type: wasm_encoder::ValType::I32,
            mutable: true,
            shared: false,
         },
         &ConstExpr::i32_const(offset as i32),
      );
      global_names.append(0, "stack_pointer");

      let mut i: u32 = 1;
      for global in program.non_stack_var_info.iter() {
         if !generation_context.var_to_slot.contains_key(global.0) {
            continue;
         }

         let wt = type_to_wasm_type_basic(&global.1.expr_type.e_type);

         let initial_val = if let Some(initializer) = global.1.initializer {
            literal_as_wasm_const(initializer, &mut generation_context)
         } else {
            match wt {
               ValType::I32 => ConstExpr::i32_const(0),
               ValType::I64 => ConstExpr::i64_const(0),
               ValType::F32 => ConstExpr::f32_const(0.0),
               ValType::F64 => ConstExpr::f64_const(0.0),
               _ => unreachable!(),
            }
         };

         globals.global(
            GlobalType {
               val_type: wt,
               mutable: true,
               shared: false,
            },
            &initial_val,
         );
         global_names.append(
            i,
            interner.lookup(program.non_stack_var_info.get(global.0).unwrap().name),
         );
         debug_assert!(generation_context.var_to_slot[global.0] == VarSlot::Register(i));
         i += 1;
      }

      (globals, global_names)
   };

   for (id, builtin_procedure) in program
      .procedures
      .iter()
      .filter(|(_, v)| v.impl_source == ProcImplSource::Builtin)
   {
      generation_context.active_fcn = Function::new_with_locals_types([]);

      match interner.lookup(builtin_procedure.definition.name.str) {
         "wasm_memory_size" => {
            generation_context.active_fcn.instruction(&Instruction::MemorySize(0));
         }
         "wasm_memory_grow" => {
            generation_context.active_fcn.instruction(&Instruction::LocalGet(0));
            generation_context.active_fcn.instruction(&Instruction::MemoryGrow(0));
         }
         "sqrt_f64" => {
            generation_context.active_fcn.instruction(&Instruction::LocalGet(0));
            generation_context.active_fcn.instruction(&Instruction::F64Sqrt);
         }
         "sqrt_f32" => {
            generation_context.active_fcn.instruction(&Instruction::LocalGet(0));
            generation_context.active_fcn.instruction(&Instruction::F32Sqrt);
         }
         "unreachable" => {
            generation_context.active_fcn.instruction(&Instruction::Unreachable);
         }
         _ => {
            // *sigh* we used to assert here, but this is actually reachable when a
            // builtin with no backend impl is referenced in the IR without a direct call
            // x = proc_name;
            continue;
         }
      }

      generation_context.active_fcn.instruction(&Instruction::End);

      function_section.function(
         generation_context
            .type_manager
            .register_or_find_type_by_definition(&builtin_procedure.definition),
      );
      generation_context.procedure_indices.insert(id);
      code_section.function(&generation_context.active_fcn);
   }

   // One pass over all procedures first so that call expressions know what index to use
   for (id, procedure) in program
      .procedures
      .iter()
      .filter(|(_, v)| v.impl_source == ProcImplSource::Native)
   {
      function_section.function(
         generation_context
            .type_manager
            .register_or_find_type_by_definition(&procedure.definition),
      );
      generation_context.procedure_indices.insert(id);
   }

   for (proc_id, procedure) in program.procedures.iter() {
      let Some(cfg) = program.procedure_bodies.get(proc_id).map(|x| &x.cfg) else {
         continue;
      };
      generation_context.active_fcn =
         Function::new_with_locals_types(regalloc_result.procedure_registers.remove(proc_id).unwrap());
      generation_context.stack_offsets_mem.clear();

      generation_context.sum_sizeof_locals_mem = 0;

      let mut mem_info: IndexMap<usize, (u32, u32)> = regalloc_result.procedure_stack_slots[proc_id]
         .iter()
         .enumerate()
         .map(|(i, x)| (i, (x.1, x.0)))
         .collect();

      mem_info.sort_by(|_k_1_, v_1, _k_2_, v_2| compare_alignment(v_1.0, v_1.1, v_2.0, v_2.1));

      for local in mem_info.iter() {
         // last element could have been a struct, and so we need to pad
         generation_context.sum_sizeof_locals_mem =
            aligned_address(generation_context.sum_sizeof_locals_mem, local.1 .0);
         generation_context
            .stack_offsets_mem
            .insert(*local.0, generation_context.sum_sizeof_locals_mem);

         generation_context.sum_sizeof_locals_mem += local.1 .1;
      }

      adjust_stack_function_entry(&mut generation_context);

      // Copy stack parameters to memory
      let mut values_index = 0;
      for param in &procedure.definition.parameters {
         if sizeof_type_values(
            &param.p_type.e_type,
            generation_context.user_defined_types,
            generation_context.target,
         ) == 0
         {
            continue;
         }
         if get_stack_address_of_local(param.var_id, &mut generation_context) {
            generation_context
               .active_fcn
               .instruction(&Instruction::LocalGet(values_index));
            store_mem(&param.p_type.e_type, &mut generation_context);
         }
         values_index += 1;
      }

      let rpo: Vec<usize> = post_order(cfg).into_iter().rev().collect();
      generation_context.cfg_index_to_rpo_index.clear();
      generation_context
         .cfg_index_to_rpo_index
         .extend(rpo.iter().enumerate().map(|(i, x)| (*x, i)));
      let dominator_tree = compute_dominators(cfg, &rpo, &generation_context.cfg_index_to_rpo_index);
      do_tree(0, &dominator_tree, &rpo, cfg, &mut generation_context);
      generation_context.active_fcn.instruction(&Instruction::Unreachable);
      generation_context.active_fcn.instruction(&Instruction::End);

      code_section.function(&generation_context.active_fcn);
   }

   let (table_section, element_section) = {
      let mut table = TableSection::new();
      let mut elem = ElementSection::new();

      let table_type = TableType {
         element_type: RefType::FUNCREF,
         minimum: generation_context.procedure_to_table_index.len() as u64,
         maximum: Some(generation_context.procedure_to_table_index.len() as u64),
         table64: false,
         shared: false,
      };

      // we always emit this table even if there are no procedures in it
      // this is because the user can write code that calls an invalid procedure pointer
      // (such as via transmute) and we still want such code to compile
      // (even if it will invariably be a runtime error when executed)
      table.table(table_type);

      if !generation_context.procedure_to_table_index.is_empty() {
         let elements = generation_context
            .procedure_to_table_index
            .iter()
            .map(|x| generation_context.procedure_indices.get_index_of(x).unwrap() as u32)
            .collect::<Vec<_>>();
         elem.active(Some(0), &ConstExpr::i32_const(0), Elements::Functions(&elements));
      }

      (table, elem)
   };

   // target specific imports/exports
   match config.target {
      Target::Lib | Target::Qbe => unreachable!(),
      Target::Wasm4 => {
         import_section.import(
            "env",
            "memory",
            EntityType::Memory(MemoryType {
               minimum: 1,
               maximum: Some(1),
               memory64: false,
               shared: false,
               page_size_log2: None,
            }),
         );
         export_section.export(
            "update",
            wasm_encoder::ExportKind::Func,
            name_to_procedure_index("update", interner, &generation_context).unwrap(),
         );
         if let Some(idx) = name_to_procedure_index("start", interner, &generation_context) {
            export_section.export("start", wasm_encoder::ExportKind::Func, idx);
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
               page_size_log2: None,
            }),
         );
         export_section.export(
            "upd",
            wasm_encoder::ExportKind::Func,
            name_to_procedure_index("upd", interner, &generation_context).unwrap(),
         );
         if let Some(idx) = name_to_procedure_index("snd", interner, &generation_context) {
            export_section.export("snd", wasm_encoder::ExportKind::Func, idx);
         }
      }
      Target::Wasi => {
         memory_section.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
         });
         export_section.export("memory", wasm_encoder::ExportKind::Memory, 0);
         export_section.export(
            "_start",
            wasm_encoder::ExportKind::Func,
            name_to_procedure_index("main", interner, &generation_context).unwrap(),
         );
      }
   }

   let name_section = {
      let mut name_section = NameSection::new();

      let mut function_names = NameMap::new();
      for (i, roland_proc_id) in generation_context.procedure_indices.iter().copied().enumerate() {
         let name_str = interner.lookup(program.procedures.get(roland_proc_id).unwrap().definition.name.str);
         function_names.append(i as u32, name_str);
      }
      name_section.functions(&function_names);

      name_section.globals(&global_names);

      name_section
   };

   let mut module = Module::new();

   module.section(&generation_context.type_manager.type_section);
   module.section(&import_section);
   module.section(&function_section);
   module.section(&table_section);
   module.section(&memory_section);
   module.section(&global_section);
   module.section(&export_section);
   // start section
   module.section(&element_section);
   // datacount section
   module.section(&code_section);
   module.section(&data_section);

   module.section(&name_section);

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

fn is_merge_node(rpo_index: usize, rpo: &[usize], cfg: &Cfg, cfg_index_to_rpo_index: &HashMap<usize, usize>) -> bool {
   cfg.bbs[rpo[rpo_index]]
      .predecessors
      .iter()
      .filter_map(|x| cfg_index_to_rpo_index.get(x).copied())
      .filter(|pred_rpo_index| *pred_rpo_index < rpo_index)
      .count()
      > 1
}

fn do_tree(
   rpo_index: usize,
   dominator_tree: &DominatorTree,
   rpo: &[usize],
   cfg: &Cfg,
   generation_context: &mut GenerationContext,
) {
   let empty_children = IndexSet::new();
   let merge_node_children: Vec<usize> = dominator_tree
      .children
      .get(&rpo_index)
      .unwrap_or(&empty_children)
      .iter()
      .copied()
      .filter(|child| is_merge_node(*child, rpo, cfg, &generation_context.cfg_index_to_rpo_index))
      .collect();
   let is_loop_header = cfg.bbs[rpo[rpo_index]].predecessors.iter().any(|pred| {
      let Some(pred_rpo_index) = generation_context.cfg_index_to_rpo_index.get(pred).copied() else {
         return false;
      };
      pred_rpo_index >= rpo_index
   });

   if is_loop_header {
      generation_context
         .active_fcn
         .instruction(&Instruction::Loop(BlockType::Empty));
      generation_context
         .frames
         .push(ContainingSyntax::LoopHeadedBy(rpo_index));
   }

   node_within(
      &merge_node_children,
      rpo_index,
      dominator_tree,
      rpo,
      cfg,
      generation_context,
   );

   if is_loop_header {
      generation_context.active_fcn.instruction(&Instruction::End);
      generation_context.frames.pop();
   }
}

fn node_within(
   merge_node_children: &[usize],
   rpo_index: usize,
   dominator_tree: &DominatorTree,
   rpo: &[usize],
   cfg: &Cfg,
   generation_context: &mut GenerationContext,
) {
   if let Some(merge_node_child) = merge_node_children.first().copied() {
      generation_context
         .active_fcn
         .instruction(&Instruction::Block(BlockType::Empty));
      generation_context
         .frames
         .push(ContainingSyntax::BlockFollowedBy(merge_node_child));
      node_within(
         &merge_node_children[1..],
         rpo_index,
         dominator_tree,
         rpo,
         cfg,
         generation_context,
      );
      generation_context.frames.pop();
      generation_context.active_fcn.instruction(&Instruction::End);
      do_tree(merge_node_child, dominator_tree, rpo, cfg, generation_context);
      return;
   }

   for instr in cfg.bbs[rpo[rpo_index]].instructions.iter() {
      match instr {
         CfgInstruction::ConditionalJump(condition, then, otherwise) => {
            do_emit(*condition, generation_context);
            generation_context.frames.push(ContainingSyntax::IfThenElse);
            generation_context
               .active_fcn
               .instruction(&Instruction::If(BlockType::Empty));
            do_branch(
               rpo_index,
               generation_context.cfg_index_to_rpo_index[then],
               dominator_tree,
               rpo,
               cfg,
               generation_context,
            );
            // else
            generation_context.active_fcn.instruction(&Instruction::Else);
            do_branch(
               rpo_index,
               generation_context.cfg_index_to_rpo_index[otherwise],
               dominator_tree,
               rpo,
               cfg,
               generation_context,
            );
            // finish if
            generation_context.frames.pop();
            generation_context.active_fcn.instruction(&Instruction::End);
         }
         CfgInstruction::Jump(x) if *x == CFG_END_NODE => (),
         CfgInstruction::Jump(target) => {
            do_branch(
               rpo_index,
               generation_context.cfg_index_to_rpo_index[target],
               dominator_tree,
               rpo,
               cfg,
               generation_context,
            );
         }
         CfgInstruction::Assignment(len, en) => {
            do_emit(*len, generation_context);
            do_emit(*en, generation_context);
            let val_type = generation_context.ast.expressions[*en].exp_type.as_ref().unwrap();
            if let Some((is_global, a_reg)) = register_for_var(*len, generation_context) {
               if is_global {
                  generation_context
                     .active_fcn
                     .instruction(&Instruction::GlobalSet(a_reg));
               } else {
                  generation_context.active_fcn.instruction(&Instruction::LocalSet(a_reg));
               }
            } else {
               store_mem(val_type, generation_context);
            }
         }
         CfgInstruction::Expression(en) => {
            do_emit(*en, generation_context);
            for _ in 0..sizeof_type_values(
               generation_context.ast.expressions[*en].exp_type.as_ref().unwrap(),
               generation_context.user_defined_types,
               generation_context.target,
            ) {
               generation_context.active_fcn.instruction(&Instruction::Drop);
            }
         }
         CfgInstruction::Return(en) => {
            do_emit(*en, generation_context);

            if generation_context.ast.expressions[*en]
               .exp_type
               .as_ref()
               .unwrap()
               .is_never()
            {
               // We have already emitted a literal "unreachable", no need to adjust the stack
            } else {
               adjust_stack_function_exit(generation_context);
               generation_context.active_fcn.instruction(&Instruction::Return);
            }
         }
         CfgInstruction::Nop => (),
      }
   }
}

fn do_branch(
   source_rpo_index: usize,
   target_rpo_index: usize,
   dominator_tree: &DominatorTree,
   rpo: &[usize],
   cfg: &Cfg,
   generation_context: &mut GenerationContext,
) {
   if target_rpo_index <= source_rpo_index
      || is_merge_node(target_rpo_index, rpo, cfg, &generation_context.cfg_index_to_rpo_index)
   {
      // continue or exit
      let index = generation_context
         .frames
         .iter()
         .copied()
         .rev()
         .position(|x| match x {
            ContainingSyntax::IfThenElse => false,
            ContainingSyntax::LoopHeadedBy(l) | ContainingSyntax::BlockFollowedBy(l) => l == target_rpo_index,
         })
         .unwrap();
      generation_context
         .active_fcn
         .instruction(&Instruction::Br(index as u32));
   } else {
      do_tree(target_rpo_index, dominator_tree, rpo, cfg, generation_context);
   }
}

fn register_for_var(expr_id: ExpressionId, generation_context: &GenerationContext) -> Option<(bool, u32)> {
   let node = &generation_context.ast.expressions[expr_id];
   match &node.expression {
      Expression::Variable(v) => generation_context
         .var_to_slot
         .get(v)
         .and_then(|x| if let VarSlot::Register(v) = x { Some(*v) } else { None })
         .map(|x| (generation_context.global_info.contains_key(v), x)),
      _ => None,
   }
}

fn literal_as_bytes(buf: &mut Vec<u8>, expr_index: ExpressionId, generation_context: &mut GenerationContext) {
   let expr_node = &generation_context.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::BoundFcnLiteral(proc_id, _) => {
         let (my_index, _) = generation_context.procedure_to_table_index.insert_full(*proc_id);
         // todo: truncation
         buf.extend((my_index as u32).to_le_bytes());
      }
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(x) => {
         buf.extend(u8::from(*x).to_le_bytes());
      }
      Expression::IntLiteral { val: x, .. } => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => x.width,
            ExpressionType::Pointer(_) => IntWidth::Four,
            _ => unreachable!(),
         };
         match width {
            IntWidth::Eight => {
               buf.extend(x.to_le_bytes());
            }
            IntWidth::Four => {
               buf.extend((*x as u32).to_le_bytes());
            }
            IntWidth::Two => {
               buf.extend((*x as u16).to_le_bytes());
            }
            IntWidth::One => {
               buf.extend((*x as u8).to_le_bytes());
            }
            IntWidth::Pointer => unreachable!(),
         };
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
      Expression::StructLiteral(s_id, fields) => {
         let si = generation_context.user_defined_types.struct_info.get(*s_id).unwrap();
         let ssi = generation_context
            .user_defined_types
            .struct_info
            .get(*s_id)
            .unwrap()
            .size
            .as_ref()
            .unwrap();
         for (field, next_offset) in si.field_types.iter().zip(
            si.field_types
               .keys()
               .skip(1)
               .map(|x| ssi.field_offsets_mem[x])
               .chain(std::iter::once(ssi.mem_size)),
         ) {
            let value_of_field = fields.get(field.0).copied().unwrap();
            if let Some(val) = value_of_field {
               literal_as_bytes(buf, val, generation_context);
            } else {
               type_as_zero_bytes(
                  buf,
                  &field.1.e_type,
                  generation_context.user_defined_types,
                  generation_context.target,
               );
            }
            let this_offset = ssi.field_offsets_mem.get(field.0).unwrap();
            let padding_bytes = next_offset
               - this_offset
               - sizeof_type_mem(
                  &field.1.e_type,
                  generation_context.user_defined_types,
                  generation_context.target,
               );
            for _ in 0..padding_bytes {
               buf.push(0);
            }
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            literal_as_bytes(buf, *expr, generation_context);
         }
      }
      _ => unreachable!(),
   }
}

fn type_as_zero_bytes(buf: &mut Vec<u8>, expr_type: &ExpressionType, udt: &UserDefinedTypeInfo, target: Target) {
   let size = sizeof_type_mem(expr_type, udt, target);
   buf.extend(std::iter::repeat(0).take(size as usize));
}

fn literal_as_wasm_const(expr_index: ExpressionId, generation_context: &mut GenerationContext) -> ConstExpr {
   let expr_node = &generation_context.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::BoundFcnLiteral(proc_id, _) => {
         let (my_index, _) = generation_context.procedure_to_table_index.insert_full(*proc_id);
         // todo: truncation
         ConstExpr::i32_const(my_index as i32)
      }
      Expression::BoolLiteral(x) => ConstExpr::i32_const(i32::from(*x)),
      Expression::IntLiteral { val: x, .. } => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => x.width,
            _ => unreachable!(),
         };
         match width {
            IntWidth::Eight => ConstExpr::i64_const(*x as i64),
            IntWidth::Four | IntWidth::Two | IntWidth::One => ConstExpr::i32_const(*x as u32 as i32),
            IntWidth::Pointer => unreachable!(),
         }
      }
      Expression::FloatLiteral(x) => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Float(x) => x.width,
            _ => unreachable!(),
         };
         match width {
            FloatWidth::Eight => ConstExpr::f64_const(*x),
            FloatWidth::Four => ConstExpr::f32_const(*x as f32),
         }
      }
      _ => unreachable!(),
   }
}

fn do_emit(expr_index: ExpressionId, generation_context: &mut GenerationContext) {
   let expr_node = &generation_context.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::UnitLiteral => (),
      Expression::IfX(a, b, c) => {
         do_emit(*a, generation_context);
         let ifx_type = generation_context
            .type_manager
            .register_or_find_type(&[], expr_node.exp_type.as_ref().unwrap());
         generation_context
            .active_fcn
            .instruction(&Instruction::If(BlockType::FunctionType(ifx_type)));
         // then
         do_emit(*b, generation_context);
         // else
         generation_context.active_fcn.instruction(&Instruction::Else);
         do_emit(*c, generation_context);
         // finish if
         generation_context.active_fcn.instruction(&Instruction::End);
      }
      Expression::BoundFcnLiteral(proc_id, _bound_type_params) => {
         if let ExpressionType::ProcedurePointer { .. } = expr_node.exp_type.as_ref().unwrap() {
            emit_procedure_pointer_index(*proc_id, generation_context);
         }
      }
      Expression::BoolLiteral(x) => {
         generation_context
            .active_fcn
            .instruction(&Instruction::I32Const(i32::from(*x)));
      }
      Expression::IntLiteral { val: x, .. } => {
         let wasm_type = type_to_wasm_type_basic(expr_node.exp_type.as_ref().unwrap());
         match wasm_type {
            ValType::I64 => generation_context
               .active_fcn
               .instruction(&Instruction::I64Const(*x as i64)),
            ValType::I32 => generation_context
               .active_fcn
               .instruction(&Instruction::I32Const(*x as i32)),
            _ => unreachable!(),
         };
      }
      Expression::FloatLiteral(x) => {
         match *expr_node.exp_type.as_ref().unwrap() {
            F64_TYPE => generation_context.active_fcn.instruction(&Instruction::F64Const(*x)),
            F32_TYPE => generation_context
               .active_fcn
               .instruction(&Instruction::F32Const(*x as f32)),
            _ => unreachable!(),
         };
      }
      Expression::StringLiteral(str) => {
         let (offset, _) = generation_context.literal_offsets.get(str).unwrap();
         generation_context
            .active_fcn
            .instruction(&Instruction::I32Const(*offset as i32));
      }
      Expression::BinaryOperator { operator, lhs, rhs } => {
         do_emit(*lhs, generation_context);

         do_emit(*rhs, generation_context);

         let (wasm_type, signed) = match generation_context.ast.expressions[*lhs].exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => match x.width {
               IntWidth::Eight => (ValType::I64, x.signed),
               _ => (ValType::I32, x.signed),
            },
            ExpressionType::Float(x) => match x.width {
               FloatWidth::Eight => (ValType::F64, false),
               FloatWidth::Four => (ValType::F32, false),
            },
            ExpressionType::Bool => (ValType::I32, false),
            _ => unreachable!(),
         };

         if matches!(operator, BinOp::BitwiseLeftShift) {
            let op_type = generation_context.ast.expressions[*rhs].exp_type.as_ref().unwrap();
            if let ExpressionType::Int(x) = op_type {
               match x.width {
                  IntWidth::Two => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I32Const(0b1111));
                     generation_context.active_fcn.instruction(&Instruction::I32And);
                  }
                  IntWidth::One => {
                     generation_context.active_fcn.instruction(&Instruction::I32Const(0b111));
                     generation_context.active_fcn.instruction(&Instruction::I32And);
                  }
                  _ => (),
               }
            }
         }

         match operator {
            BinOp::Add => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Add),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Add),
                  ValType::F64 => generation_context.active_fcn.instruction(&Instruction::F64Add),
                  ValType::F32 => generation_context.active_fcn.instruction(&Instruction::F32Add),
                  _ => unreachable!(),
               };
            }
            BinOp::Subtract => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Sub),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Sub),
                  ValType::F64 => generation_context.active_fcn.instruction(&Instruction::F64Sub),
                  ValType::F32 => generation_context.active_fcn.instruction(&Instruction::F32Sub),
                  _ => unreachable!(),
               };
            }
            BinOp::Multiply => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Mul),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Mul),
                  ValType::F64 => generation_context.active_fcn.instruction(&Instruction::F64Mul),
                  ValType::F32 => generation_context.active_fcn.instruction(&Instruction::F32Mul),
                  _ => unreachable!(),
               };
            }
            BinOp::Divide => {
               match (wasm_type, signed) {
                  (ValType::I64, true) => generation_context.active_fcn.instruction(&Instruction::I64DivS),
                  (ValType::I32, true) => generation_context.active_fcn.instruction(&Instruction::I32DivS),
                  (ValType::I64, false) => generation_context.active_fcn.instruction(&Instruction::I64DivU),
                  (ValType::I32, false) => generation_context.active_fcn.instruction(&Instruction::I32DivU),
                  (ValType::F64, _) => generation_context.active_fcn.instruction(&Instruction::F64Div),
                  (ValType::F32, _) => generation_context.active_fcn.instruction(&Instruction::F32Div),
                  _ => unreachable!(),
               };
            }
            BinOp::Remainder => {
               match (wasm_type, signed) {
                  (ValType::I64, true) => generation_context.active_fcn.instruction(&Instruction::I64RemS),
                  (ValType::I32, true) => generation_context.active_fcn.instruction(&Instruction::I32RemS),
                  (ValType::I64, false) => generation_context.active_fcn.instruction(&Instruction::I64RemU),
                  (ValType::I32, false) => generation_context.active_fcn.instruction(&Instruction::I32RemU),
                  _ => unreachable!(),
               };
            }
            BinOp::Equality => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Eq),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Eq),
                  ValType::F64 => generation_context.active_fcn.instruction(&Instruction::F64Eq),
                  ValType::F32 => generation_context.active_fcn.instruction(&Instruction::F32Eq),
                  _ => unreachable!(),
               };
            }
            BinOp::NotEquality => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Ne),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Ne),
                  ValType::F64 => generation_context.active_fcn.instruction(&Instruction::F64Ne),
                  ValType::F32 => generation_context.active_fcn.instruction(&Instruction::F32Ne),
                  _ => unreachable!(),
               };
            }
            BinOp::GreaterThan => {
               match (wasm_type, signed) {
                  (ValType::I64, true) => generation_context.active_fcn.instruction(&Instruction::I64GtS),
                  (ValType::I32, true) => generation_context.active_fcn.instruction(&Instruction::I32GtS),
                  (ValType::I64, false) => generation_context.active_fcn.instruction(&Instruction::I64GtU),
                  (ValType::I32, false) => generation_context.active_fcn.instruction(&Instruction::I32GtU),
                  (ValType::F64, _) => generation_context.active_fcn.instruction(&Instruction::F64Gt),
                  (ValType::F32, _) => generation_context.active_fcn.instruction(&Instruction::F32Gt),
                  _ => unreachable!(),
               };
            }
            BinOp::GreaterThanOrEqualTo => {
               match (wasm_type, signed) {
                  (ValType::I64, true) => generation_context.active_fcn.instruction(&Instruction::I64GeS),
                  (ValType::I32, true) => generation_context.active_fcn.instruction(&Instruction::I32GeS),
                  (ValType::I64, false) => generation_context.active_fcn.instruction(&Instruction::I64GeU),
                  (ValType::I32, false) => generation_context.active_fcn.instruction(&Instruction::I32GeU),
                  (ValType::F64, _) => generation_context.active_fcn.instruction(&Instruction::F64Ge),
                  (ValType::F32, _) => generation_context.active_fcn.instruction(&Instruction::F32Ge),
                  _ => unreachable!(),
               };
            }
            BinOp::LessThan => {
               match (wasm_type, signed) {
                  (ValType::I64, true) => generation_context.active_fcn.instruction(&Instruction::I64LtS),
                  (ValType::I32, true) => generation_context.active_fcn.instruction(&Instruction::I32LtS),
                  (ValType::I64, false) => generation_context.active_fcn.instruction(&Instruction::I64LtU),
                  (ValType::I32, false) => generation_context.active_fcn.instruction(&Instruction::I32LtU),
                  (ValType::F64, _) => generation_context.active_fcn.instruction(&Instruction::F64Lt),
                  (ValType::F32, _) => generation_context.active_fcn.instruction(&Instruction::F32Lt),
                  _ => unreachable!(),
               };
            }
            BinOp::LessThanOrEqualTo => {
               match (wasm_type, signed) {
                  (ValType::I64, true) => generation_context.active_fcn.instruction(&Instruction::I64LeS),
                  (ValType::I32, true) => generation_context.active_fcn.instruction(&Instruction::I32LeS),
                  (ValType::I64, false) => generation_context.active_fcn.instruction(&Instruction::I64LeU),
                  (ValType::I32, false) => generation_context.active_fcn.instruction(&Instruction::I32LeU),
                  (ValType::F64, _) => generation_context.active_fcn.instruction(&Instruction::F64Le),
                  (ValType::F32, _) => generation_context.active_fcn.instruction(&Instruction::F32Le),
                  _ => unreachable!(),
               };
            }
            BinOp::BitwiseAnd => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64And),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32And),
                  _ => unreachable!(),
               };
            }
            BinOp::BitwiseOr => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Or),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Or),
                  _ => unreachable!(),
               };
            }
            BinOp::BitwiseXor => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Xor),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Xor),
                  _ => unreachable!(),
               };
            }
            BinOp::BitwiseLeftShift => {
               match wasm_type {
                  ValType::I64 => generation_context.active_fcn.instruction(&Instruction::I64Shl),
                  ValType::I32 => generation_context.active_fcn.instruction(&Instruction::I32Shl),
                  _ => unreachable!(),
               };
            }
            BinOp::BitwiseRightShift => {
               match (wasm_type, signed) {
                  (ValType::I64, true) => generation_context.active_fcn.instruction(&Instruction::I64ShrS),
                  (ValType::I32, true) => generation_context.active_fcn.instruction(&Instruction::I32ShrS),
                  (ValType::I64, false) => generation_context.active_fcn.instruction(&Instruction::I64ShrU),
                  (ValType::I32, false) => generation_context.active_fcn.instruction(&Instruction::I32ShrU),
                  _ => unreachable!(),
               };
            }
            BinOp::LogicalAnd | BinOp::LogicalOr => unreachable!(),
         }

         if matches!(operator, BinOp::Add | BinOp::Multiply | BinOp::Subtract) {
            let op_type = generation_context.ast.expressions[*lhs].exp_type.as_ref().unwrap();
            if let ExpressionType::Int(x) = op_type {
               // Emulate overflow for necessary types
               match (x.width, x.signed) {
                  (IntWidth::Two, true) => {
                     generation_context.active_fcn.instruction(&Instruction::I32Extend16S);
                  }
                  (IntWidth::Two, false) => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_1111_1111_1111_1111));
                     generation_context.active_fcn.instruction(&Instruction::I32And);
                  }
                  (IntWidth::One, true) => {
                     generation_context.active_fcn.instruction(&Instruction::I32Extend8S);
                  }
                  (IntWidth::One, false) => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_0000_0000_1111_1111));
                     generation_context.active_fcn.instruction(&Instruction::I32And);
                  }
                  _ => (),
               }
            }
         }
      }
      Expression::UnaryOperator(un_op, e_index) => {
         let e = &generation_context.ast.expressions[*e_index];

         match un_op {
            UnOp::TakeProcedurePointer => {
               let ExpressionType::ProcedureItem(proc_id, _bound_type_params) = e.exp_type.as_ref().unwrap() else {
                  unreachable!();
               };
               emit_procedure_pointer_index(*proc_id, generation_context);
            }
            UnOp::Dereference => {
               do_emit(*e_index, generation_context);

               if let Some((is_global, a_reg)) = register_for_var(*e_index, generation_context) {
                  if is_global {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::GlobalGet(a_reg));
                  } else {
                     generation_context.active_fcn.instruction(&Instruction::LocalGet(a_reg));
                  }
               } else {
                  load_mem(expr_node.exp_type.as_ref().unwrap(), generation_context);
               }
            }
            UnOp::Complement => {
               let wasm_type = type_to_wasm_type_basic(expr_node.exp_type.as_ref().unwrap());
               do_emit(*e_index, generation_context);

               if *e.exp_type.as_ref().unwrap() == ExpressionType::Bool {
                  generation_context.active_fcn.instruction(&Instruction::I32Eqz);
               } else {
                  complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
               }
            }
            UnOp::Negate => {
               let wasm_type = type_to_wasm_type_basic(expr_node.exp_type.as_ref().unwrap());
               do_emit(*e_index, generation_context);

               match wasm_type {
                  ValType::I64 => {
                     complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
                     generation_context.active_fcn.instruction(&Instruction::I64Const(1));
                     generation_context.active_fcn.instruction(&Instruction::I64Add);
                  }
                  ValType::I32 => {
                     complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
                     generation_context.active_fcn.instruction(&Instruction::I32Const(1));
                     generation_context.active_fcn.instruction(&Instruction::I32Add);
                  }
                  ValType::F64 => {
                     generation_context.active_fcn.instruction(&Instruction::F64Neg);
                  }
                  ValType::F32 => {
                     generation_context.active_fcn.instruction(&Instruction::F32Neg);
                  }
                  _ => unreachable!(),
               }
            }
            UnOp::AddressOf => unreachable!(),
         }
      }
      Expression::Cast {
         cast_type: CastType::Transmute,
         expr: e_id,
         ..
      } => {
         let e = &generation_context.ast.expressions[*e_id];
         let target_type = expr_node.exp_type.as_ref().unwrap();

         do_emit(*e_id, generation_context);

         if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Float(_))
            && matches!(target_type, ExpressionType::Int(_))
         {
            // float -> int
            match target_type {
               ExpressionType::Int(x) if x.width.as_num_bytes(generation_context.target) == 4 => {
                  generation_context
                     .active_fcn
                     .instruction(&Instruction::I32ReinterpretF32);
               }
               ExpressionType::Int(x) if x.width.as_num_bytes(generation_context.target) == 8 => {
                  generation_context
                     .active_fcn
                     .instruction(&Instruction::I64ReinterpretF64);
               }
               _ => unreachable!(),
            }
         } else if matches!(e.exp_type.as_ref().unwrap(), ExpressionType::Int(_))
            && matches!(target_type, ExpressionType::Float(_))
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
      Expression::Cast {
         cast_type: CastType::As,
         expr: e,
         ..
      } => {
         do_emit(*e, generation_context);

         let e = &generation_context.ast.expressions[*e];

         let src_type = e.exp_type.as_ref().unwrap();
         let target_type = expr_node.exp_type.as_ref().unwrap();

         if src_type == target_type {
            return;
         }

         match (src_type, target_type) {
            (ExpressionType::Int(l), ExpressionType::Int(r))
               if l.width.as_num_bytes(generation_context.target)
                  >= r.width.as_num_bytes(generation_context.target) =>
            {
               match (l.width, r.width) {
                  (IntWidth::Eight, IntWidth::Four) => {
                     generation_context.active_fcn.instruction(&Instruction::I32WrapI64);
                  }
                  (IntWidth::Eight, IntWidth::Two) => {
                     generation_context.active_fcn.instruction(&Instruction::I32WrapI64);
                     if r.signed {
                        generation_context.active_fcn.instruction(&Instruction::I32Extend16S);
                     } else {
                        generation_context
                           .active_fcn
                           .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_1111_1111_1111_1111));
                        generation_context.active_fcn.instruction(&Instruction::I32And);
                     }
                  }
                  (IntWidth::Eight, IntWidth::One) => {
                     generation_context.active_fcn.instruction(&Instruction::I32WrapI64);
                     if r.signed {
                        generation_context.active_fcn.instruction(&Instruction::I32Extend8S);
                     } else {
                        generation_context
                           .active_fcn
                           .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_0000_0000_1111_1111));
                        generation_context.active_fcn.instruction(&Instruction::I32And);
                     }
                  }
                  (IntWidth::Four, IntWidth::Two) => {
                     if r.signed {
                        generation_context.active_fcn.instruction(&Instruction::I32Extend16S);
                     } else {
                        generation_context
                           .active_fcn
                           .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_1111_1111_1111_1111));
                        generation_context.active_fcn.instruction(&Instruction::I32And);
                     }
                  }
                  (IntWidth::Four | IntWidth::Two, IntWidth::One) => {
                     if r.signed {
                        generation_context.active_fcn.instruction(&Instruction::I32Extend8S);
                     } else {
                        generation_context
                           .active_fcn
                           .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_0000_0000_1111_1111));
                        generation_context.active_fcn.instruction(&Instruction::I32And);
                     }
                  }
                  (IntWidth::Two, IntWidth::Two) => {
                     if !l.signed && r.signed {
                        generation_context.active_fcn.instruction(&Instruction::I32Extend16S);
                     } else if l.signed && !r.signed {
                        generation_context
                           .active_fcn
                           .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_1111_1111_1111_1111));
                        generation_context.active_fcn.instruction(&Instruction::I32And);
                     }
                  }
                  (IntWidth::One, IntWidth::One) => {
                     if !l.signed && r.signed {
                        generation_context.active_fcn.instruction(&Instruction::I32Extend8S);
                     } else if l.signed && !r.signed {
                        generation_context
                           .active_fcn
                           .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_0000_0000_1111_1111));
                        generation_context.active_fcn.instruction(&Instruction::I32And);
                     }
                  }
                  _ => (),
               }
            }
            (ExpressionType::Int(l), ExpressionType::Int(r))
               if l.width.as_num_bytes(generation_context.target) < r.width.as_num_bytes(generation_context.target) =>
            {
               if l.width.as_num_bytes(generation_context.target) <= 4 && r.width == IntWidth::Eight {
                  if l.signed {
                     generation_context.active_fcn.instruction(&Instruction::I64ExtendI32S);
                  } else {
                     generation_context.active_fcn.instruction(&Instruction::I64ExtendI32U);
                  }
               } else if l.width == IntWidth::One && r.width == IntWidth::Two && l.signed && !r.signed {
                  generation_context
                     .active_fcn
                     .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_1111_1111_1111_1111));
                  generation_context.active_fcn.instruction(&Instruction::I32And);
               }
            }
            (&F64_TYPE, &F32_TYPE) => {
               generation_context.active_fcn.instruction(&Instruction::F32DemoteF64);
            }
            (&F32_TYPE, &F64_TYPE) => {
               generation_context.active_fcn.instruction(&Instruction::F64PromoteF32);
            }
            (
               ExpressionType::Float(FloatType { width: src_width }),
               ExpressionType::Int(IntType {
                  signed,
                  width: dest_width,
               }),
            ) => {
               match src_width {
                  FloatWidth::Eight => {
                     match (dest_width, signed) {
                        (IntWidth::Eight, true) => {
                           generation_context.active_fcn.instruction(&Instruction::I64TruncSatF64S)
                        }
                        (IntWidth::Eight, false) => {
                           generation_context.active_fcn.instruction(&Instruction::I64TruncSatF64U)
                        }
                        (_, true) => generation_context.active_fcn.instruction(&Instruction::I32TruncSatF64S),
                        (_, false) => generation_context.active_fcn.instruction(&Instruction::I32TruncSatF64U),
                     };
                  }
                  FloatWidth::Four => {
                     match (dest_width, signed) {
                        (IntWidth::Eight, true) => {
                           generation_context.active_fcn.instruction(&Instruction::I64TruncSatF32S)
                        }
                        (IntWidth::Eight, false) => {
                           generation_context.active_fcn.instruction(&Instruction::I64TruncSatF32U)
                        }
                        (_, true) => generation_context.active_fcn.instruction(&Instruction::I32TruncSatF32S),
                        (_, false) => generation_context.active_fcn.instruction(&Instruction::I32TruncSatF32U),
                     };
                  }
               }
               match dest_width {
                  IntWidth::Eight | IntWidth::Four => (),
                  IntWidth::Two => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_1111_1111_1111_1111));
                     generation_context.active_fcn.instruction(&Instruction::I32And);
                  }
                  IntWidth::One => {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::I32Const(0b0000_0000_0000_0000_0000_0000_1111_1111));
                     generation_context.active_fcn.instruction(&Instruction::I32And);
                  }
                  IntWidth::Pointer => unreachable!(),
               }
            }
            (
               ExpressionType::Int(IntType {
                  signed,
                  width: src_width,
               }),
               ExpressionType::Float(FloatType { width: dest_width }),
            ) => match dest_width {
               FloatWidth::Eight => {
                  match (src_width, signed) {
                     (IntWidth::Eight, true) => generation_context.active_fcn.instruction(&Instruction::F64ConvertI64S),
                     (IntWidth::Eight, false) => {
                        generation_context.active_fcn.instruction(&Instruction::F64ConvertI64U)
                     }
                     (_, true) => generation_context.active_fcn.instruction(&Instruction::F64ConvertI32S),
                     (_, false) => generation_context.active_fcn.instruction(&Instruction::F64ConvertI32U),
                  };
               }
               FloatWidth::Four => {
                  match (src_width, signed) {
                     (IntWidth::Eight, true) => generation_context.active_fcn.instruction(&Instruction::F32ConvertI64S),
                     (IntWidth::Eight, false) => {
                        generation_context.active_fcn.instruction(&Instruction::F32ConvertI64U)
                     }
                     (_, true) => generation_context.active_fcn.instruction(&Instruction::F32ConvertI32S),
                     (_, false) => generation_context.active_fcn.instruction(&Instruction::F32ConvertI32U),
                  };
               }
            },
            (ExpressionType::Bool, ExpressionType::Int(i)) => {
               if i.width == IntWidth::Eight {
                  generation_context.active_fcn.instruction(&Instruction::I64ExtendI32U);
               }
            }
            _ => unreachable!(),
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
      Expression::ProcedureCall { proc_expr, args } => {
         match generation_context.ast.expressions[*proc_expr]
            .exp_type
            .as_ref()
            .unwrap()
         {
            ExpressionType::ProcedureItem(proc_name, _) => {
               do_emit(*proc_expr, generation_context);
               for arg in args.iter() {
                  do_emit(arg.expr, generation_context);
               }
               let idx = generation_context.procedure_indices.get_index_of(proc_name).unwrap() as u32;
               generation_context.active_fcn.instruction(&Instruction::Call(idx));
            }
            ExpressionType::ProcedurePointer { parameters, ret_type } => {
               for arg in args.iter() {
                  do_emit(arg.expr, generation_context);
               }
               do_emit(*proc_expr, generation_context);
               let type_index = generation_context
                  .type_manager
                  .register_or_find_type(parameters.iter(), ret_type);
               generation_context.active_fcn.instruction(&Instruction::CallIndirect {
                  type_index,
                  table_index: 0,
               });
            }
            _ => unreachable!(),
         };
      }
      Expression::FieldAccess(field_name, lhs_id) => {
         fn calculate_offset(lhs_type: &ExpressionType, field_name: StrId, generation_context: &mut GenerationContext) {
            let mem_offset = match lhs_type.get_type_or_type_being_pointed_to() {
               ExpressionType::Struct(s, _) => *generation_context
                  .user_defined_types
                  .struct_info
                  .get(*s)
                  .unwrap()
                  .size
                  .as_ref()
                  .unwrap()
                  .field_offsets_mem
                  .get(&field_name)
                  .unwrap(),
               ExpressionType::Union(_, _) => 0,
               _ => unreachable!(),
            };

            generation_context.emit_const_add_i32(mem_offset);
         }

         let lhs = &generation_context.ast.expressions[*lhs_id];

         do_emit(*lhs_id, generation_context);
         // TODO: for an expression like foo.bar.baz, we will emit 3 const adds, when they should be fused
         calculate_offset(lhs.exp_type.as_ref().unwrap(), *field_name, generation_context);
      }
      Expression::ArrayIndex { array, index } => {
         fn calculate_offset(array: ExpressionId, index_e: ExpressionId, generation_context: &mut GenerationContext) {
            let sizeof_inner = match generation_context.ast.expressions[array].exp_type.as_ref().unwrap().get_type_or_type_being_pointed_to() {
               ExpressionType::Array(x, _) => {
                  sizeof_type_mem(x, generation_context.user_defined_types, generation_context.target)
               }
               _ => unreachable!(),
            };

            if let Expression::IntLiteral { val: x, .. } = generation_context.ast.expressions[index_e].expression {
               // Safe assert due to inference and constant folding validating this
               let val_32 = u32::try_from(x).unwrap();
               let result = sizeof_inner.wrapping_mul(val_32);
               generation_context.emit_const_add_i32(result);
            } else {
               do_emit(index_e, generation_context);
               generation_context.emit_const_mul_i32(sizeof_inner);
               generation_context.active_fcn.instruction(&Instruction::I32Add);
            }
         }

         do_emit(*array, generation_context);
         calculate_offset(*array, *index, generation_context);
      }
      Expression::EnumLiteral(_, _)
      | Expression::StructLiteral(_, _)
      | Expression::ArrayLiteral(_)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
   if expr_node.exp_type.as_ref().unwrap().is_never() {
      generation_context.active_fcn.instruction(&Instruction::Unreachable);
   }
}

fn complement_val(t_type: &ExpressionType, wasm_type: ValType, generation_context: &mut GenerationContext) {
   let magic_const: u64 = match *t_type {
      crate::type_data::U8_TYPE => u64::from(u8::MAX),
      crate::type_data::U16_TYPE => u64::from(u16::MAX),
      crate::type_data::U32_TYPE
      | crate::type_data::I8_TYPE
      | crate::type_data::I16_TYPE
      | crate::type_data::I32_TYPE => u64::from(u32::MAX),
      crate::type_data::I64_TYPE | crate::type_data::U64_TYPE => u64::MAX,
      _ => unreachable!(),
   };
   match wasm_type {
      ValType::I32 => {
         generation_context
            .active_fcn
            .instruction(&Instruction::I32Const(magic_const as u32 as i32));
         generation_context.active_fcn.instruction(&Instruction::I32Xor);
      }
      ValType::I64 => {
         generation_context
            .active_fcn
            .instruction(&Instruction::I64Const(magic_const as i64));
         generation_context.active_fcn.instruction(&Instruction::I64Xor);
      }
      _ => unreachable!(),
   }
}

/// Places the address of given local on the stack
fn get_stack_address_of_local(id: VariableId, generation_context: &mut GenerationContext) -> bool {
   let Some(VarSlot::Stack(s)) = generation_context.var_to_slot.get(&id) else {
      return false;
   };
   let offset = aligned_address(generation_context.sum_sizeof_locals_mem, 8)
      - generation_context
         .stack_offsets_mem
         .get(&(*s as usize))
         .copied()
         .unwrap();
   generation_context.active_fcn.instruction(&Instruction::GlobalGet(SP));
   generation_context.emit_const_sub_i32(offset);
   true
}

fn load_mem(val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   if sizeof_type_values(
      val_type,
      generation_context.user_defined_types,
      generation_context.target,
   ) == 0
   {
      // Drop the load address; nothing to load
      generation_context.active_fcn.instruction(&Instruction::Drop);
      return;
   }

   if val_type.is_aggregate() {
      // Leave the address on the stack - there is no value representation of aggregates
      // (Storing code understands this)
      return;
   }

   if sizeof_type_mem(
      val_type,
      generation_context.user_defined_types,
      generation_context.target,
   ) == sizeof_type_wasm(
      val_type,
      generation_context.user_defined_types,
      generation_context.target,
   ) {
      match type_to_wasm_type_basic(val_type) {
         ValType::I64 => generation_context
            .active_fcn
            .instruction(&Instruction::I64Load(null_mem_arg())),
         ValType::I32 => generation_context
            .active_fcn
            .instruction(&Instruction::I32Load(null_mem_arg())),
         ValType::F64 => generation_context
            .active_fcn
            .instruction(&Instruction::F64Load(null_mem_arg())),
         ValType::F32 => generation_context
            .active_fcn
            .instruction(&Instruction::F32Load(null_mem_arg())),
         _ => unreachable!(),
      };
   } else {
      match val_type {
         ExpressionType::Int(x) => match (x.width, x.signed) {
            (IntWidth::Two, true) => generation_context
               .active_fcn
               .instruction(&Instruction::I32Load16S(null_mem_arg())),
            (IntWidth::Two, false) => generation_context
               .active_fcn
               .instruction(&Instruction::I32Load16U(null_mem_arg())),
            (IntWidth::One, true) => generation_context
               .active_fcn
               .instruction(&Instruction::I32Load8S(null_mem_arg())),
            (IntWidth::One, false) => generation_context
               .active_fcn
               .instruction(&Instruction::I32Load8U(null_mem_arg())),
            _ => unreachable!(),
         },
         ExpressionType::Bool => generation_context
            .active_fcn
            .instruction(&Instruction::I32Load8U(null_mem_arg())),
         _ => unreachable!(),
      };
   }
}

fn store_mem(val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   debug_assert!(
      sizeof_type_values(
         val_type,
         generation_context.user_defined_types,
         generation_context.target
      ) != 0
   );

   // say that we have y = x~
   // and x is NOT an aggregate type
   // but x~ IS
   // loading x~ produces a val
   // so far OK.
   // but then we try to store into y
   // y is an aggregate. no register
   // RHS type is an aggregate
   // so it does a memcpy.
   // but memcpy is wrong. the thing we loaded is not an address. we just want to do a normal store.
   // our type based query is failing us.
   // need to think what to do
   if val_type.is_aggregate() {
      let size = sizeof_type_mem(
         val_type,
         generation_context.user_defined_types,
         generation_context.target,
      );
      generation_context
         .active_fcn
         .instruction(&Instruction::I32Const(size as i32));
      generation_context
         .active_fcn
         .instruction(&Instruction::MemoryCopy { src_mem: 0, dst_mem: 0 });
      return;
   }

   if sizeof_type_mem(
      val_type,
      generation_context.user_defined_types,
      generation_context.target,
   ) == sizeof_type_wasm(
      val_type,
      generation_context.user_defined_types,
      generation_context.target,
   ) {
      match type_to_wasm_type_basic(val_type) {
         ValType::I64 => generation_context
            .active_fcn
            .instruction(&Instruction::I64Store(null_mem_arg())),
         ValType::I32 => generation_context
            .active_fcn
            .instruction(&Instruction::I32Store(null_mem_arg())),
         ValType::F64 => generation_context
            .active_fcn
            .instruction(&Instruction::F64Store(null_mem_arg())),
         ValType::F32 => generation_context
            .active_fcn
            .instruction(&Instruction::F32Store(null_mem_arg())),
         _ => unreachable!(),
      };
   } else {
      match val_type {
         ExpressionType::Int(x) => match x.width {
            IntWidth::Two => generation_context
               .active_fcn
               .instruction(&Instruction::I32Store16(null_mem_arg())),
            IntWidth::One => generation_context
               .active_fcn
               .instruction(&Instruction::I32Store8(null_mem_arg())),
            _ => unreachable!(),
         },
         ExpressionType::Bool => generation_context
            .active_fcn
            .instruction(&Instruction::I32Store8(null_mem_arg())),
         _ => unreachable!(),
      };
   }
}

fn adjust_stack_function_entry(generation_context: &mut GenerationContext) {
   adjust_stack(generation_context, &Instruction::I32Add);
}

fn adjust_stack_function_exit(generation_context: &mut GenerationContext) {
   adjust_stack(generation_context, &Instruction::I32Sub);
}

fn adjust_stack(generation_context: &mut GenerationContext, instr: &Instruction) {
   if generation_context.sum_sizeof_locals_mem == 0 {
      return;
   }

   generation_context.active_fcn.instruction(&Instruction::GlobalGet(SP));
   // ensure that each stack frame is strictly aligned so that internal stack frame alignment is preserved
   let adjust_value = aligned_address(generation_context.sum_sizeof_locals_mem, 8);
   generation_context
      .active_fcn
      .instruction(&Instruction::I32Const(adjust_value as i32));
   generation_context.active_fcn.instruction(instr);
   generation_context.active_fcn.instruction(&Instruction::GlobalSet(SP));
}

fn emit_procedure_pointer_index(proc_id: ProcedureId, generation_context: &mut GenerationContext) {
   let (my_index, _) = generation_context.procedure_to_table_index.insert_full(proc_id);
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

fn name_to_procedure_index(
   name: &'static str,
   interner: &mut Interner,
   generation_context: &GenerationContext,
) -> Option<u32> {
   let id = generation_context.proc_name_table.get(&interner.intern(name))?;
   Some(generation_context.procedure_indices.get_index_of(id).unwrap() as u32)
}
