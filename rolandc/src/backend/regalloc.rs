use std::collections::HashSet;

use indexmap::IndexMap;
use slotmap::SecondaryMap;
use wasm_encoder::ValType;

use super::liveness::liveness;
use crate::backend::linearize::linearize;
use crate::backend::wasm::type_to_wasm_type;
use crate::expression_hoisting::is_wasm_compatible_rval_transmute;
use crate::interner::Interner;
use crate::parse::{
   AstPool, BlockNode, CastType, Expression, ExpressionId, ExpressionPool, ProcImplSource, ProcedureId, Statement,
   StatementId, UnOp, VariableId,
};
use crate::{Program, Target};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct ProgramIndex(usize);

impl PartialOrd for ProgramIndex {
   fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      Some(self.cmp(other))
   }
}

impl Ord for ProgramIndex {
   fn cmp(&self, other: &Self) -> std::cmp::Ordering {
      self.0.cmp(&other.0)
   }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct LiveRange {
   begin: ProgramIndex,
   end: ProgramIndex,
}

struct RegallocCtx {
   escaping_vars: HashSet<VariableId>,
}

pub struct RegallocResult {
   pub var_to_reg: IndexMap<VariableId, Vec<u32>>,
   pub procedure_registers: SecondaryMap<ProcedureId, Vec<ValType>>,
}

pub fn assign_variables_to_wasm_registers(
   program: &mut Program,
   interner: &Interner,
   target: Target,
) -> RegallocResult {
   let program_cfg = linearize(program, interner);

   let mut ctx = RegallocCtx {
      escaping_vars: HashSet::new(),
   };

   let mut result = RegallocResult {
      var_to_reg: IndexMap::new(),
      procedure_registers: SecondaryMap::with_capacity(program.procedures.len()),
   };

   let mut active: Vec<VariableId> = Vec::new();
   let mut free_registers: IndexMap<ValType, Vec<u32>> = IndexMap::new();
   let mut t_buf: Vec<ValType> = Vec::new();

   for (proc_id, procedure) in program.procedures.iter() {
      result.procedure_registers.insert(proc_id, Vec::new());
      let all_registers = result.procedure_registers.get_mut(proc_id).unwrap();
      let mut total_registers = 0;

      free_registers.clear();

      let ProcImplSource::Body(block) = &procedure.proc_impl else {
         continue;
      };

      liveness(&program_cfg[proc_id], &program.global_info);
      mark_escaping_vars_block(block, &mut ctx, &program.ast);

      let mut live_ranges: IndexMap<VariableId, LiveRange> = IndexMap::new();
      live_ranges.sort_unstable_by(|_, v1, _, v2| v1.begin.cmp(&v2.begin));

      active.clear();

      // All parameters start in registers because that's how WASM
      // (and Roland's calling convention) work.
      for param in procedure.definition.parameters.iter() {
         let var = param.var_id;
         let typ = &param.p_type.e_type;

         t_buf.clear();
         type_to_wasm_type(typ, &mut t_buf, &program.struct_info);

         let reg = total_registers;
         total_registers += t_buf.len() as u32;

         if ctx.escaping_vars.contains(&var) {
            // address is observed, variable must live on the stack.
            // however, this var is a parameter, so we still need to offset
            // the register count
            continue;
         }

         result.var_to_reg.insert(var, (reg..total_registers).collect());
      }

      for (var, range) in live_ranges.iter() {
         if result.var_to_reg.contains_key(var) {
            // (This local is a parameter, which inherently has a register)
            continue;
         }

         if ctx.escaping_vars.contains(var) {
            // address is observed, variable must live on the stack
            continue;
         }

         for expired_var in active.extract_if(|v| live_ranges.get(v).unwrap().end < range.begin) {
            t_buf.clear();
            type_to_wasm_type(
               procedure.locals.get(&expired_var).unwrap(),
               &mut t_buf,
               &program.struct_info,
            );
            for (t_val, reg) in t_buf.drain(..).zip(result.var_to_reg.get(&expired_var).unwrap()) {
               free_registers.entry(t_val).or_default().push(*reg);
            }
         }

         t_buf.clear();
         type_to_wasm_type(procedure.locals.get(var).unwrap(), &mut t_buf, &program.struct_info);

         let mut var_registers = Vec::with_capacity(t_buf.len());
         for t_val in t_buf.drain(..) {
            let reg = if let Some(reg) = free_registers.entry(t_val).or_default().pop() {
               reg
            } else {
               all_registers.push(t_val);
               let reg = total_registers;
               total_registers += 1;
               reg
            };

            var_registers.push(reg);
         }

         result.var_to_reg.insert(*var, var_registers.clone());
         active.push(*var);
      }
   }

   if target == Target::Wasm4 {
      // Force global variables to live in memory for WASM4, because globals
      // are not synchronized by the netplay engine
      return result;
   }

   let mut num_global_registers = 2; // Skip the base pointer, mem address globals
   for global in program.global_info.iter() {
      debug_assert!(!result.var_to_reg.contains_key(global.0));

      if ctx.escaping_vars.contains(global.0) {
         continue;
      }

      t_buf.clear();
      type_to_wasm_type(&global.1.expr_type.e_type, &mut t_buf, &program.struct_info);

      let reg = num_global_registers;
      num_global_registers += t_buf.len() as u32;

      result
         .var_to_reg
         .insert(*global.0, (reg..num_global_registers).collect());
   }

   result
}

fn mark_escaping_vars_block(block: &BlockNode, ctx: &mut RegallocCtx, ast: &AstPool) {
   for statement in block.statements.iter().rev().copied() {
      mark_escaping_vars_statement(statement, ctx, ast);
   }
}

fn mark_escaping_vars_statement(stmt: StatementId, ctx: &mut RegallocCtx, ast: &AstPool) {
   match &ast.statements[stmt].statement {
      Statement::Return(expr) => {
         mark_escaping_vars_expr(*expr, ctx, ast);
      }
      Statement::Break | Statement::Continue => (),
      Statement::Block(block) => {
         mark_escaping_vars_block(block, ctx, ast);
      }
      Statement::IfElse(if_expr, if_block, else_statement) => {
         mark_escaping_vars_expr(*if_expr, ctx, ast);
         mark_escaping_vars_block(if_block, ctx, ast);
         mark_escaping_vars_statement(*else_statement, ctx, ast);
      }
      Statement::Loop(body) => {
         mark_escaping_vars_block(body, ctx, ast);
      }
      Statement::Assignment(lhs, rhs) => {
         mark_escaping_vars_expr(*lhs, ctx, ast);
         mark_escaping_vars_expr(*rhs, ctx, ast);
      }
      Statement::Expression(expr) => {
         mark_escaping_vars_expr(*expr, ctx, ast);
      }
      Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
   }
}

fn mark_escaping_vars_expr(in_expr: ExpressionId, ctx: &mut RegallocCtx, ast: &AstPool) {
   match &ast.expressions[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         mark_escaping_vars_expr(*proc_expr, ctx, ast);

         for val in args.iter().map(|x| x.expr) {
            mark_escaping_vars_expr(val, ctx, ast);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            mark_escaping_vars_expr(val, ctx, ast);
         }
      }
      Expression::ArrayIndex { array, index } => {
         mark_escaping_vars_expr(*array, ctx, ast);
         mark_escaping_vars_expr(*index, ctx, ast);

         if let Some(v) = get_var_from_use(*array, &ast.expressions) {
            if !matches!(ast.expressions[*index].expression, Expression::IntLiteral { .. }) {
               ctx.escaping_vars.insert(v);
            }
         }
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         mark_escaping_vars_expr(*lhs, ctx, ast);
         mark_escaping_vars_expr(*rhs, ctx, ast);
      }
      Expression::IfX(a, b, c) => {
         mark_escaping_vars_expr(*a, ctx, ast);
         mark_escaping_vars_expr(*b, ctx, ast);
         mark_escaping_vars_expr(*c, ctx, ast);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            mark_escaping_vars_expr(*expr, ctx, ast);
         }
      }
      Expression::FieldAccess(_, base_expr) => {
         mark_escaping_vars_expr(*base_expr, ctx, ast);
      }
      Expression::Cast { expr, cast_type, .. } => {
         mark_escaping_vars_expr(*expr, ctx, ast);

         if *cast_type == CastType::Transmute
            && !is_wasm_compatible_rval_transmute(
               ast.expressions[*expr].exp_type.as_ref().unwrap(),
               ast.expressions[in_expr].exp_type.as_ref().unwrap(),
            )
         {
            if let Some(v) = get_var_from_use(*expr, &ast.expressions) {
               ctx.escaping_vars.insert(v);
            }
         }
      }
      Expression::UnaryOperator(op, expr) => {
         mark_escaping_vars_expr(*expr, ctx, ast);
         if *op == UnOp::AddressOf {
            if let Some(v) = get_var_from_use(*expr, &ast.expressions) {
               ctx.escaping_vars.insert(v);
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
      Expression::UnresolvedStructLiteral(_, _) => unreachable!(),
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
