use std::collections::HashSet;

use indexmap::IndexMap;
use slotmap::SecondaryMap;
use wasm_encoder::ValType;

use super::linearize::{post_order, Cfg, CfgInstruction};
use super::liveness::{liveness, ProgramIndex};
use crate::expression_hoisting::is_reinterpretable_transmute;
use crate::parse::{
   AstPool, CastType, Expression, ExpressionId, ExpressionPool, ProcImplSource, ProcedureId, UnOp, VariableId,
};
use crate::size_info::sizeof_type_mem;
use crate::type_data::{ExpressionType, FloatWidth, IntWidth};
use crate::{CompilationConfig, Program, Target};

pub struct RegallocResult {
   pub var_to_reg: IndexMap<VariableId, u32>,
   pub procedure_registers: SecondaryMap<ProcedureId, Vec<ValType>>,
}

pub fn assign_variables_to_wasm_registers(program: &Program, config: &CompilationConfig) -> RegallocResult {
   let mut escaping_vars = HashSet::new();

   let mut result = RegallocResult {
      var_to_reg: IndexMap::new(),
      procedure_registers: SecondaryMap::with_capacity(program.procedures.len()),
   };

   let mut active: Vec<VariableId> = Vec::new();
   let mut free_registers: IndexMap<ValType, Vec<u32>> = IndexMap::new();

   for (proc_id, procedure) in program.procedures.iter() {
      active.clear();
      free_registers.clear();

      result.procedure_registers.insert(proc_id, Vec::new());
      let all_registers = result.procedure_registers.get_mut(proc_id).unwrap();
      let mut total_registers = 0;

      if !matches!(&procedure.proc_impl, ProcImplSource::Body(_)) {
         continue;
      }

      mark_escaping_vars_cfg(&program.cfg[proc_id], &mut escaping_vars, &program.ast);

      let mut live_intervals: IndexMap<VariableId, LiveInterval> = IndexMap::with_capacity(procedure.locals.len());
      {
         let proc_liveness = liveness(&procedure.locals, &program.cfg[proc_id], &program.ast);

         for (pi, live_vars) in proc_liveness.iter() {
            for local_index in live_vars.iter_ones() {
               let var = procedure.locals.get_index(local_index).map(|x| *x.0).unwrap();
               if let Some(existing_range) = live_intervals.get_mut(&var) {
                  existing_range.begin = std::cmp::min(existing_range.begin, *pi);
                  existing_range.end = std::cmp::max(existing_range.end, *pi);
               } else {
                  live_intervals.insert(var, LiveInterval { begin: *pi, end: *pi });
               }
            }
         }
         live_intervals.sort_unstable_by(|_, v1, _, v2| v1.begin.cmp(&v2.begin));
      }

      // All non-aggregate parameters start in registers because that's how WASM
      // (and Roland's calling convention) work.
      for param in procedure.definition.parameters.iter() {
         let var = param.var_id;
         let typ = &param.p_type.e_type;

         if sizeof_type_mem(typ, &program.user_defined_types, config.target) == 0 {
            continue;
         }

         let reg = total_registers;
         total_registers += 1;

         if typ.is_aggregate() || escaping_vars.contains(&var) {
            // variable must live on the stack.
            // however, this var is a parameter, so we still need to offset
            // the register count
            continue;
         }

         result.var_to_reg.insert(var, reg);
      }

      for (var, range) in live_intervals.iter() {
         if result.var_to_reg.contains_key(var) {
            // We have already assigned this var to a register, which means it must be a parameter
            continue;
         }

         if escaping_vars.contains(var) {
            // address is observed, variable must live on the stack
            continue;
         }

         let local_type = procedure.locals.get(var).unwrap();
         if local_type.is_aggregate() || local_type.is_nonaggregate_zst() {
            continue;
         }

         for expired_var in active.extract_if(|v| live_intervals.get(v).unwrap().end < range.begin) {
            let wt = type_to_register_type(procedure.locals.get(&expired_var).unwrap(), config.target);
            free_registers
               .entry(wt)
               .or_default()
               .push(result.var_to_reg.get(&expired_var).copied().unwrap());
         }

         let rt = type_to_register_type(local_type, config.target);

         let reg = if let Some(reg) = free_registers.entry(rt).or_default().pop() {
            reg
         } else {
            all_registers.push(rt);
            let reg = total_registers;
            total_registers += 1;
            reg
         };

         result.var_to_reg.insert(*var, reg);
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
   for global in program.global_info.iter() {
      debug_assert!(!result.var_to_reg.contains_key(global.0));

      if escaping_vars.contains(global.0) {
         continue;
      }

      if global.1.expr_type.e_type.is_aggregate() || global.1.expr_type.e_type.is_nonaggregate_zst() {
         continue;
      }

      let reg = num_global_registers;
      num_global_registers += 1;

      result.var_to_reg.insert(*global.0, reg);
   }

   result
}

fn mark_escaping_vars_cfg(cfg: &Cfg, escaping_vars: &mut HashSet<VariableId>, ast: &AstPool) {
   for bb in post_order(cfg) {
      for instr in cfg.bbs[bb].instructions.iter() {
         match instr {
            CfgInstruction::Assignment(lhs, rhs) => {
               mark_escaping_vars_expr(*lhs, escaping_vars, ast);
               mark_escaping_vars_expr(*rhs, escaping_vars, ast);
            }
            CfgInstruction::Expression(e) => {
               mark_escaping_vars_expr(*e, escaping_vars, ast);
            }
            CfgInstruction::ConditionalJump(e, _, _) => {
               mark_escaping_vars_expr(*e, escaping_vars, ast);
            }
            CfgInstruction::Return(e) => {
               mark_escaping_vars_expr(*e, escaping_vars, ast);
            }
            CfgInstruction::IfElse(e, _, _, _) => {
               mark_escaping_vars_expr(*e, escaping_vars, ast);
            }
            _ => (),
         }
      }
   }
}

fn mark_escaping_vars_expr(in_expr: ExpressionId, escaping_vars: &mut HashSet<VariableId>, ast: &AstPool) {
   match &ast.expressions[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_escaping_vars_expr(*proc_expr, escaping_vars, ast);

         for val in args.iter().map(|x| x.expr) {
            mark_escaping_vars_expr(val, escaping_vars, ast);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            mark_escaping_vars_expr(val, escaping_vars, ast);
         }
      }
      Expression::ArrayIndex { array, index } => {
         mark_escaping_vars_expr(*array, escaping_vars, ast);
         mark_escaping_vars_expr(*index, escaping_vars, ast);

         if let Some(v) = get_var_from_use(*array, &ast.expressions) {
            if !matches!(ast.expressions[*index].expression, Expression::IntLiteral { .. }) {
               escaping_vars.insert(v);
            }
         }
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         mark_escaping_vars_expr(*lhs, escaping_vars, ast);
         mark_escaping_vars_expr(*rhs, escaping_vars, ast);
      }
      Expression::IfX(a, b, c) => {
         mark_escaping_vars_expr(*a, escaping_vars, ast);
         mark_escaping_vars_expr(*b, escaping_vars, ast);
         mark_escaping_vars_expr(*c, escaping_vars, ast);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            mark_escaping_vars_expr(*expr, escaping_vars, ast);
         }
      }
      Expression::FieldAccess(_, base_expr) => {
         mark_escaping_vars_expr(*base_expr, escaping_vars, ast);
      }
      Expression::Cast { expr, cast_type, .. } => {
         mark_escaping_vars_expr(*expr, escaping_vars, ast);

         if *cast_type == CastType::Transmute
            && !is_reinterpretable_transmute(
               ast.expressions[*expr].exp_type.as_ref().unwrap(),
               ast.expressions[in_expr].exp_type.as_ref().unwrap(),
            )
         {
            if let Some(v) = get_var_from_use(*expr, &ast.expressions) {
               escaping_vars.insert(v);
            }
         }
      }
      Expression::UnaryOperator(op, expr) => {
         mark_escaping_vars_expr(*expr, escaping_vars, ast);
         if *op == UnOp::AddressOf {
            if let Some(v) = get_var_from_use(*expr, &ast.expressions) {
               escaping_vars.insert(v);
            }
         }
      }
      Expression::Variable(_) => (),
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(_, _) => (),
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnresolvedVariable(_) | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}

fn get_var_from_use(expr: ExpressionId, expressions: &ExpressionPool) -> Option<VariableId> {
   match &expressions[expr].expression {
      Expression::Variable(v) => Some(*v),
      Expression::FieldAccess(_, e) => get_var_from_use(*e, expressions),
      Expression::ArrayIndex { array, .. } => get_var_from_use(*array, expressions),
      _ => None,
   }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct LiveInterval {
   pub begin: ProgramIndex,
   pub end: ProgramIndex,
}

// TODO: merge with type_to_wasm_type? also, create an abstraction instead of using ValType
fn type_to_register_type(et: &ExpressionType, target: Target) -> ValType {
   match et {
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
      x => {
         unreachable!("{:?}", x);
      }
   }
}
