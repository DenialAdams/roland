use std::collections::HashSet;
use std::ops::Range;

use indexmap::IndexMap;
use slotmap::SecondaryMap;
use wasm_encoder::ValType;

use crate::parse::{
   AstPool, BlockNode, CastType, Expression, ExpressionId, ExpressionPool, ProcedureId, Statement, StatementId, UnOp,
   VariableId,
};
use crate::wasm::type_to_wasm_type;
use crate::Program;

struct RegallocCtx {
   escaping_vars: HashSet<VariableId>,
}

#[derive(Clone)]
pub enum Register {
   Reg(Range<u32>),
   ZSTReg,
}

pub struct RegallocResult {
   pub var_to_reg: IndexMap<VariableId, Register>,
   pub procedure_registers: SecondaryMap<ProcedureId, Vec<ValType>>,
}

pub fn assign_variables_to_locals(program: &Program) -> RegallocResult {
   let mut ctx = RegallocCtx {
      escaping_vars: HashSet::new(),
   };

   let mut result = RegallocResult {
      var_to_reg: IndexMap::new(),
      procedure_registers: SecondaryMap::with_capacity(program.procedures.len()),
   };

   let mut t_buf: Vec<ValType> = Vec::new();

   for (proc_id, procedure) in program.procedures.iter() {
      result.procedure_registers.insert(proc_id, Vec::new());
      let all_registers = result.procedure_registers.get_mut(proc_id).unwrap();

      regalloc_block(&procedure.block, &mut ctx, &program.ast);

      for (var, typ) in procedure.locals.iter() {
         if ctx.escaping_vars.contains(var) {
            // address is observed, variable must live on the stack
            continue;
         }

         t_buf.clear();
         type_to_wasm_type(typ, &mut t_buf, &program.struct_info);

         if t_buf.is_empty() {
            result.var_to_reg.insert(*var, Register::ZSTReg);
            continue;
         } else if t_buf.len() > 1 {
            // nocheckin
            continue;
         }

         let reg = all_registers.len() as u32;
         all_registers.extend_from_slice(&t_buf);

         result.var_to_reg.insert(*var, Register::Reg(reg..all_registers.len() as u32));
      }
   }

   result
}

fn regalloc_block(block: &BlockNode, ctx: &mut RegallocCtx, ast: &AstPool) {
   for statement in block.statements.iter().copied() {
      regalloc_statement(statement, ctx, ast);
   }
}

fn regalloc_statement(stmt: StatementId, ctx: &mut RegallocCtx, ast: &AstPool) {
   match &ast.statements[stmt].statement {
      Statement::Return(expr) => {
         regalloc_expr(*expr, ctx, ast);
      }
      Statement::Break | Statement::Continue => (),
      Statement::Block(block) => {
         regalloc_block(block, ctx, ast);
      }
      Statement::IfElse(if_expr, if_block, else_statement) => {
         regalloc_expr(*if_expr, ctx, ast);
         regalloc_block(if_block, ctx, ast);
         regalloc_statement(*else_statement, ctx, ast);
      }
      Statement::Loop(body) => {
         regalloc_block(body, ctx, ast);
      }
      Statement::For {
         range_start,
         range_end,
         body,
         induction_var,
         ..
      } => {
         regalloc_expr(*range_start, ctx, ast);
         regalloc_expr(*range_end, ctx, ast);
         regalloc_block(body, ctx, ast);
         regalloc_var(*induction_var, ctx);
      }
      Statement::Assignment(lhs, rhs) => {
         regalloc_expr(*lhs, ctx, ast);
         regalloc_expr(*rhs, ctx, ast);
      }
      Statement::Expression(expr) => {
         regalloc_expr(*expr, ctx, ast);
      }
      Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
   }
}

fn regalloc_expr(in_expr: ExpressionId, ctx: &mut RegallocCtx, ast: &AstPool) {
   match &ast.expressions[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         regalloc_expr(*proc_expr, ctx, ast);

         for val in args.iter().map(|x| x.expr) {
            regalloc_expr(val, ctx, ast);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            regalloc_expr(val, ctx, ast);
         }
      }
      Expression::ArrayIndex { array, index } => {
         regalloc_expr(*array, ctx, ast);
         regalloc_expr(*index, ctx, ast);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         regalloc_expr(*lhs, ctx, ast);
         regalloc_expr(*rhs, ctx, ast);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.iter().map(|x| x.1) {
            regalloc_expr(expr, ctx, ast);
         }
      }
      Expression::FieldAccess(_, base_expr) => {
         regalloc_expr(*base_expr, ctx, ast);
      }
      Expression::Cast { expr, cast_type, .. } => {
         regalloc_expr(*expr, ctx, ast);
         if *cast_type == CastType::Transmute {
            if let Some(v) = get_var_from_lhs_expr(*expr, &ast.expressions) {
               ctx.escaping_vars.insert(v);
            }
         }
      }
      Expression::UnaryOperator(op, expr) => {
         regalloc_expr(*expr, ctx, ast);
         if *op == UnOp::AddressOf {
            if let Some(v) = get_var_from_lhs_expr(*expr, &ast.expressions) {
               ctx.escaping_vars.insert(v);
            }
         }
      }
      Expression::Variable(var) => {
         regalloc_var(*var, ctx);
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(_, _) => (),
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnresolvedVariable(_) => unreachable!(),
   }
}

fn regalloc_var(_var: VariableId, _ctx: &mut RegallocCtx) {
   // In the future, we might do some liveness analysis here.
}

pub fn get_var_from_lhs_expr(expr: ExpressionId, expressions: &ExpressionPool) -> Option<VariableId> {
   match &expressions[expr].expression {
      Expression::Variable(v) => Some(*v),
      Expression::FieldAccess(_, e) => get_var_from_lhs_expr(*e, expressions),
      Expression::ArrayIndex { array, .. } => get_var_from_lhs_expr(*array, expressions),
      _ => None,
   }
}
