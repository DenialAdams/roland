use std::collections::HashMap;

use indexmap::IndexMap;
use slotmap::SecondaryMap;
use wasm_encoder::ValType;

use super::linearize::CfgInstruction;
use super::liveness::LiveInterval;
use crate::escape_analysis::{mark_escaping_vars_cfg, EscapingKind};
use crate::parse::{Expression, ProcedureId, UserDefinedTypeInfo, VariableId};
use crate::size_info::{mem_alignment, sizeof_type_mem};
use crate::type_data::{ExpressionType, FloatWidth, IntWidth};
use crate::{CompilationConfig, Program, Target};

#[derive(Clone, Copy, PartialEq)]
pub enum VarSlot {
   Stack(u32),
   Register(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum VarSlotKind {
   Stack((u32, u32)), // (size, alignment)
   Register(ValType),
}

pub struct RegallocResult {
   pub var_to_slot: IndexMap<VariableId, VarSlot>,
   pub procedure_registers: SecondaryMap<ProcedureId, Vec<ValType>>,
   pub procedure_stack_slots: SecondaryMap<ProcedureId, Vec<(u32, u32)>>,
}

pub fn assign_variables_to_registers_and_mem(
   program: &Program,
   config: &CompilationConfig,
   program_liveness: &SecondaryMap<ProcedureId, IndexMap<VariableId, LiveInterval>>,
) -> RegallocResult {
   let mut escaping_vars = HashMap::new();

   let mut result = RegallocResult {
      var_to_slot: IndexMap::new(),
      procedure_registers: SecondaryMap::with_capacity(program.procedures.len()),
      procedure_stack_slots: SecondaryMap::with_capacity(program.procedures.len()),
   };

   let mut active: Vec<VariableId> = Vec::new();
   let mut free_slots: IndexMap<VarSlotKind, Vec<VarSlot>> = IndexMap::new();

   for (proc_id, body) in program.procedure_bodies.iter() {
      active.clear();
      free_slots.clear();

      result.procedure_registers.insert(proc_id, Vec::new());
      let all_registers = result.procedure_registers.get_mut(proc_id).unwrap();
      result.procedure_stack_slots.insert(proc_id, Vec::new());
      let all_stack_slots = result.procedure_stack_slots.get_mut(proc_id).unwrap();
      let mut total_registers = 0;
      let mut total_stack_slots = 0;

      mark_escaping_vars_cfg(&body.cfg, &mut escaping_vars, &program.ast.expressions);

      if config.target != Target::Qbe {
         // For WASM, all parameters start in registers
         for param in program.procedures[proc_id].definition.parameters.iter() {
            let var = param.var_id;
            let typ = &param.p_type.e_type;

            if sizeof_type_mem(typ, &program.user_defined_types, config.target) == 0 {
               continue;
            }

            let reg = total_registers;
            total_registers += 1;

            if typ.is_aggregate() || escaping_vars.contains_key(&var) {
               // variable must live on the stack.
               // however, this var is a parameter, so we still need to offset
               // the register count
               continue;
            }

            result.var_to_slot.insert(var, VarSlot::Register(reg));
         }
      }

      let live_intervals = &program_liveness[proc_id];
      for (var, range) in live_intervals.iter() {
         if result.var_to_slot.contains_key(var) {
            // We have already assigned this var, which means it must be a parameter
            continue;
         }

         // when extract_if is stable:
         // for expired_var in active.extract_if(|v| live_intervals.get(v).unwrap().end < range.begin)
         // and can remove following retain
         for expired_var in active
            .iter()
            .filter(|v| live_intervals.get(*v).unwrap().end < range.begin)
         {
            let escaping_kind = escaping_vars.get(expired_var).copied();
            if escaping_kind == Some(EscapingKind::MustLiveOnStackAlone) {
               continue;
            }
            let sk = type_to_slot_kind(
               body.locals.get(expired_var).unwrap(),
               escaping_kind.is_some(),
               &program.user_defined_types,
               config.target,
            );
            if matches!(sk, VarSlotKind::Stack(_)) && config.target == Target::Qbe {
               // Empirically, our stack slot re-use interferes with QBE's own
               // stack slot reuse, and results in worse ASM.
               continue;
            }
            free_slots
               .entry(sk)
               .or_default()
               .push(result.var_to_slot.get(expired_var).copied().unwrap());
         }
         active.retain(|v| live_intervals.get(v).unwrap().end >= range.begin);

         let sk = type_to_slot_kind(
            body.locals.get(var).unwrap(),
            escaping_vars.contains_key(var),
            &program.user_defined_types,
            config.target,
         );

         let slot = if let Some(slot) = free_slots.entry(sk).or_default().pop() {
            slot
         } else {
            match sk {
               VarSlotKind::Register(rt) => {
                  all_registers.push(rt);
                  let reg = total_registers;
                  total_registers += 1;
                  VarSlot::Register(reg)
               }
               VarSlotKind::Stack(sz) => {
                  all_stack_slots.push(sz);
                  let ss = total_stack_slots;
                  total_stack_slots += 1;
                  VarSlot::Stack(ss)
               }
            }
         };

         result.var_to_slot.insert(*var, slot);
         active.push(*var);
      }
   }

   if config.target != Target::Wasi {
      // We force global variables to live in memory for WASM4, because globals
      // are not synchronized by the netplay engine.
      // For QBE, there is simply no concept of global registers.
      return result;
   }

   let mut num_global_registers = 1; // Skip the stack pointer
   for global in program.non_stack_var_info.iter() {
      debug_assert!(!result.var_to_slot.contains_key(global.0));

      if escaping_vars.contains_key(global.0) {
         continue;
      }

      if global.1.expr_type.e_type.is_aggregate()
         || sizeof_type_mem(&global.1.expr_type.e_type, &program.user_defined_types, config.target) == 0
      {
         continue;
      }

      let reg = num_global_registers;
      num_global_registers += 1;

      result.var_to_slot.insert(*global.0, VarSlot::Register(reg));
   }

   result
}

fn type_to_slot_kind(
   et: &ExpressionType,
   var_is_escaping: bool,
   udt: &UserDefinedTypeInfo,
   target: Target,
) -> VarSlotKind {
   let size = sizeof_type_mem(et, udt, target);
   if et.is_aggregate() || var_is_escaping || size == 0 {
      // Minimum alignment is 4 for QBE, and that seems fine for WASM backends too
      let slot_alignment = std::cmp::max(mem_alignment(et, udt, target), 4);
      VarSlotKind::Stack((size, slot_alignment))
   } else {
      VarSlotKind::Register(match et {
         ExpressionType::Int(x) => match x.width {
            IntWidth::Eight => ValType::I64,
            _ => ValType::I32,
         },
         ExpressionType::Float(x) => match x.width {
            FloatWidth::Eight => ValType::F64,
            FloatWidth::Four => ValType::F32,
         },
         ExpressionType::Bool => ValType::I32,
         ExpressionType::ProcedurePointer { .. } => {
            if target.pointer_width() == 8 {
               ValType::I64
            } else {
               ValType::I32
            }
         }
         _ => unreachable!(),
      })
   }
}

pub fn kill_self_assignments(program: &mut Program, var_to_slot: &IndexMap<VariableId, VarSlot>) {
   for body in program.procedure_bodies.values_mut() {
      for bb in body.cfg.bbs.iter_mut() {
         for instr in bb.instructions.iter_mut() {
            let CfgInstruction::Assignment(lhs, rhs) = *instr else {
               continue;
            };
            let Expression::Variable(l_var) = program.ast.expressions[lhs].expression else {
               continue;
            };
            let Expression::Variable(r_var) = program.ast.expressions[rhs].expression else {
               continue;
            };
            let lhs_slot = var_to_slot.get(&l_var);
            let rhs_slot = var_to_slot.get(&r_var);
            if lhs_slot.is_none() || lhs_slot != rhs_slot {
               continue;
            }
            *instr = CfgInstruction::Nop;
         }
      }
   }
}
