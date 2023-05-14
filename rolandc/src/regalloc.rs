use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};
use wasm_encoder::ValType;

use crate::parse::{AstPool, BlockNode, Expression, ExpressionId, Statement, StatementId, UnOp, VariableId};
use crate::Program;
use crate::wasm::type_to_wasm_type;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct ProgramIndex {
   block: usize,
   stmt: usize,
}

impl PartialOrd for ProgramIndex {
   fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      Some(self.cmp(other))
   }
}

impl Ord for ProgramIndex {
   fn cmp(&self, other: &Self) -> std::cmp::Ordering {
      self.block.cmp(&other.block).then_with(|| self.stmt.cmp(&other.stmt))
   }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct LiveRange {
   begin: ProgramIndex,
   end: ProgramIndex,
}

impl PartialOrd for LiveRange {
   fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      Some(self.cmp(other))
   }
}

impl Ord for LiveRange {
   fn cmp(&self, other: &Self) -> std::cmp::Ordering {
      self.begin.cmp(&other.begin).then_with(|| self.end.cmp(&other.end))
   }
}

struct RegallocCtx {
   escaping_vars: HashSet<VariableId>,
   live_ranges: IndexMap<VariableId, LiveRange>,
   current_loc: ProgramIndex,
}

pub fn assign_variables_to_locals(program: &Program) -> IndexMap<VariableId, usize> {
   let mut ctx = RegallocCtx {
      escaping_vars: HashSet::new(),
      live_ranges: IndexMap::new(),
      current_loc: ProgramIndex { block: 0, stmt: 0 },
   };

   let mut active_ranges = IndexSet::new();
   let mut free_registers: IndexMap<ValType, Vec<usize>> = IndexMap::new();
   let mut used_registers: IndexMap<ValType, Vec<usize>> = IndexMap::new();
   let mut var_to_reg: IndexMap<VariableId, usize> = IndexMap::new();
   let mut t_buf: Vec<ValType> = Vec::new();

   for procedure in program.procedures.values() {
      let mut total_registers = 0;
      free_registers.clear();
      used_registers.clear();

      ctx.current_loc = ProgramIndex { block: 0, stmt: 0 };
      ctx.live_ranges.clear();
      regalloc_block(&procedure.block, &mut ctx, &program.ast);

      ctx.live_ranges.sort_unstable_by(|_, v1, _, v2| v1.cmp(v2));

      active_ranges.clear();
      for (var, range) in ctx.live_ranges.iter() {
         if ctx.escaping_vars.contains(var) {
            // address is observed, variable must live on the stack
            continue;
         }

         if !procedure.locals.contains_key(var) {
            // global variables
            continue;
         }

         t_buf.clear();
         type_to_wasm_type(procedure.locals.get(var).unwrap(), &mut t_buf, &program.struct_info);

         if t_buf.len() != 1 {
            // We skip aggregates for no good reason - 
            // if the aggregate var hasn't escaped, we can decompose the aggregate
            // into registers. But, that does take some effort
            continue;
         }

         // TODO: expire live ranges

         let reg = if let Some(reg) = free_registers.entry(t_buf[0]).or_default().pop() {
            used_registers.entry(t_buf[0]).and_modify(|x| x.push(reg));
            reg
         } else {
            used_registers.entry(t_buf[0]).and_modify(|x| x.push(total_registers));
            let val = total_registers;
            total_registers += 1;
            val
         };

         var_to_reg.insert(*var, reg);

         active_ranges.insert(*range);
      }
   }

   var_to_reg
}

fn regalloc_block(block: &BlockNode, ctx: &mut RegallocCtx, ast: &AstPool) {
   let saved_location = ctx.current_loc;
   ctx.current_loc.block += 1;
   for statement in block.statements.iter().copied() {
      ctx.current_loc.stmt += 1;
      regalloc_statement(statement, ctx, ast);
   }
   ctx.current_loc = saved_location;
}

fn regalloc_statement(stmt: StatementId, ctx: &mut RegallocCtx, ast: &AstPool) {
   ctx.current_loc.stmt += 1;
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
      Expression::Cast { expr, .. } => {
         regalloc_expr(*expr, ctx, ast);
      }
      Expression::UnaryOperator(op, expr) => {
         regalloc_expr(*expr, ctx, ast);
         if *op == UnOp::AddressOf {
            match ast.expressions[*expr].expression {
               Expression::Variable(v) => {
                  ctx.escaping_vars.insert(v);
               }
               Expression::FieldAccess(_, e) => {
                  if let Expression::Variable(v) = ast.expressions[e].expression {
                     ctx.escaping_vars.insert(v);
                  }
               }
               _ => (),
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

fn regalloc_var(var: VariableId, ctx: &mut RegallocCtx) {
   if let Some(existing_range) = ctx.live_ranges.get_mut(&var) {
      existing_range.end = ctx.current_loc;
   } else {
      ctx.live_ranges.insert(
         var,
         LiveRange {
            begin: ctx.current_loc,
            end: ctx.current_loc,
         },
      );
   }
}
