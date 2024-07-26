use std::collections::{HashMap, HashSet};

use arrayvec::ArrayVec;

use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::Interner;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionNode, ExpressionPool, Statement, StatementId,
};
use crate::type_data::ExpressionType;
use crate::{Program, Target};

// TODO: This is pretty bulky. Ideally this would be size <= 8 for storage in the BB.
#[derive(Clone)]
pub enum CfgInstruction {
   Assignment(ExpressionId, ExpressionId),
   Expression(ExpressionId),
   ConditionalJump(ExpressionId, usize, usize),
   Jump(usize),
   Return(ExpressionId),
   Nop,
}

#[derive(Clone)]
pub struct BasicBlock {
   pub instructions: Vec<CfgInstruction>,
   // TODO: let's make this a bitset?
   pub predecessors: HashSet<usize>,
}

impl BasicBlock {
   pub fn successors(&self) -> ArrayVec<usize, 2> {
      let mut buf = ArrayVec::new();
      if let Some(x) = self.instructions.last() {
         match x {
            CfgInstruction::ConditionalJump(_, a, b) => {
               buf.push(*a);
               buf.push(*b);
            }
            CfgInstruction::Jump(x) => {
               buf.push(*x);
            }
            _ => (),
         }
      }

      buf
   }
}

pub const CFG_END_NODE: usize = 1;

#[derive(Clone)]
pub struct Cfg {
   pub bbs: Vec<BasicBlock>,
   pub start: usize,
}

struct Ctx {
   bbs: Vec<BasicBlock>,
   current_block: usize,
   break_target: usize,
   continue_target: usize,
}

pub fn simplify_cfg(cfg: &mut Cfg, ast: &ExpressionPool) {
   for node in post_order(cfg) {
      if cfg.bbs[node].instructions.len() != 1 {
         continue;
      }

      let dest = if let Some(CfgInstruction::Jump(dest)) = cfg.bbs[node].instructions.last() {
         *dest
      } else {
         continue;
      };

      if cfg.start == node {
         cfg.start = dest;
      }

      let preds = std::mem::take(&mut cfg.bbs[node].predecessors);
      for pred in preds {
         if pred == node {
            cfg.bbs[node].predecessors.insert(pred);
            continue;
         }
         let last_in_pred = cfg.bbs[pred].instructions.pop().unwrap();
         match last_in_pred {
            CfgInstruction::ConditionalJump(cond_expr, mut x, mut y) => {
               if x == node {
                  x = dest;
               } else {
                  debug_assert!(y == node);
                  y = dest;
               }
               if x == y {
                  if expression_could_have_side_effects(cond_expr, ast) {
                     cfg.bbs[pred].instructions.push(CfgInstruction::Expression(cond_expr));
                  }
                  cfg.bbs[pred].instructions.push(CfgInstruction::Jump(dest));
               } else {
                  cfg.bbs[pred]
                     .instructions
                     .push(CfgInstruction::ConditionalJump(cond_expr, x, y));
               }
            }
            CfgInstruction::Jump(_) => {
               cfg.bbs[pred].instructions.push(CfgInstruction::Jump(dest));
            }
            _ => unreachable!(),
         }
         cfg.bbs[dest].predecessors.insert(pred);
         cfg.bbs[dest].predecessors.remove(&node);
      }
   }
}

fn dump_program_cfg(interner: &Interner, program: &Program) {
   let mut f = std::fs::File::create("cfg.dot").unwrap();
   for (proc, body) in program.procedure_bodies.iter() {
      use std::io::Write;
      writeln!(
         f,
         "digraph {} {{",
         interner.lookup(program.procedures[proc].definition.name.str)
      )
      .unwrap();
      let rpo: Vec<usize> = post_order(&body.cfg).into_iter().rev().collect();
      let cfg_index_to_rpo_index: HashMap<usize, usize> = rpo.iter().enumerate().map(|(i, x)| (*x, i)).collect();
      for (rpo_index, node) in rpo.iter().copied().enumerate() {
         let successors = body.cfg.bbs[node].successors();
         for succ in successors.iter() {
            writeln!(
               f,
               "\"{}\" -> \"{}\"",
               bb_id_to_label(rpo_index),
               bb_id_to_label(cfg_index_to_rpo_index[succ])
            )
            .unwrap();
         }
      }
      writeln!(f, "}}").unwrap();
   }
}

pub fn linearize(program: &mut Program, interner: &Interner, dump_cfg: bool, target: Target) {
   let mut ctx = Ctx {
      bbs: vec![],
      current_block: 0,
      break_target: 0,
      continue_target: 0,
   };
   for (id, body) in program.procedure_bodies.iter_mut() {
      ctx.bbs.push(BasicBlock {
         instructions: vec![],
         predecessors: HashSet::new(),
      });
      ctx.bbs.push(BasicBlock {
         instructions: vec![],
         predecessors: HashSet::new(),
      });
      ctx.current_block = 0;

      if !linearize_block(&mut ctx, &body.block, &mut program.ast, target) {
         let location = program.procedures[id].location;
         let return_expr = program.ast.expressions.insert(ExpressionNode {
            expression: Expression::UnitLiteral,
            exp_type: Some(ExpressionType::Never),
            location,
         });
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Return(return_expr));
      }

      body.cfg.bbs = std::mem::take(&mut ctx.bbs);

      if target == Target::Qbe {
         // We don't simplify the CFG for WASM targets, since
         // simplification can result in the structured control flow
         // statements going out of sync with their corresponding
         // jumps.
         simplify_cfg(&mut body.cfg, &program.ast.expressions);
      }
   }

   if dump_cfg {
      dump_program_cfg(interner, program);
   }
}

fn bb_id_to_label(bb_id: usize) -> String {
   let tformed = (bb_id + 65) as u8 as char;
   if tformed == '\\' {
      String::from("\\\\")
   } else {
      String::from(tformed)
   }
}

pub fn post_order(cfg: &Cfg) -> Vec<usize> {
   let mut visited = HashSet::with_capacity(cfg.bbs.len());
   let mut post_order = Vec::with_capacity(cfg.bbs.len());
   post_order_inner(&cfg.bbs, cfg.start, &mut visited, &mut post_order);
   post_order
}

fn post_order_inner(cfg: &[BasicBlock], node: usize, visited: &mut HashSet<usize>, post_order: &mut Vec<usize>) {
   let successors = cfg[node].successors();

   visited.insert(node);
   for succ in successors {
      if !visited.contains(&succ) {
         post_order_inner(cfg, succ, visited, post_order);
      }
   }

   post_order.push(node);
}

#[must_use]
fn linearize_block(ctx: &mut Ctx, block: &BlockNode, ast: &mut AstPool, target: Target) -> bool {
   for stmt in block.statements.iter() {
      if linearize_stmt(ctx, *stmt, ast, target) {
         return true;
      }
   }

   false
}

#[must_use]
fn linearize_stmt(ctx: &mut Ctx, stmt: StatementId, ast: &mut AstPool, target: Target) -> bool {
   let borrowed_stmt = std::mem::replace(&mut ast.statements[stmt].statement, Statement::Break);
   let sealed = match &borrowed_stmt {
      Statement::IfElse(condition, consequent, alternative) => {
         let then_dest = ctx.bbs.len();
         let else_dest = then_dest + 1;
         let afterwards_dest = then_dest + 2;
         ctx.bbs.push(BasicBlock {
            instructions: vec![],
            predecessors: HashSet::new(),
         });
         ctx.bbs.push(BasicBlock {
            instructions: vec![],
            predecessors: HashSet::new(),
         });
         ctx.bbs.push(BasicBlock {
            instructions: vec![],
            predecessors: HashSet::new(),
         });
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::ConditionalJump(*condition, then_dest, else_dest));
         ctx.bbs[then_dest].predecessors.insert(ctx.current_block);
         ctx.bbs[else_dest].predecessors.insert(ctx.current_block);

         ctx.current_block = then_dest;
         if !linearize_block(ctx, consequent, ast, target) {
            ctx.bbs[ctx.current_block]
               .instructions
               .push(CfgInstruction::Jump(afterwards_dest));
            ctx.bbs[afterwards_dest].predecessors.insert(ctx.current_block);
         }

         ctx.current_block = else_dest;
         if !linearize_stmt(ctx, *alternative, ast, target) {
            ctx.bbs[ctx.current_block]
               .instructions
               .push(CfgInstruction::Jump(afterwards_dest));
            ctx.bbs[afterwards_dest].predecessors.insert(ctx.current_block);
         }

         ctx.current_block = afterwards_dest;

         false
      }
      Statement::Loop(bn) => {
         let old_cont_target = ctx.continue_target;
         let old_break_target = ctx.break_target;

         ctx.continue_target = ctx.bbs.len();
         ctx.break_target = ctx.continue_target + 1;
         ctx.bbs.push(BasicBlock {
            instructions: vec![],
            predecessors: HashSet::new(),
         });
         ctx.bbs.push(BasicBlock {
            instructions: vec![],
            predecessors: HashSet::new(),
         });

         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Jump(ctx.continue_target));
         ctx.bbs[ctx.continue_target].predecessors.insert(ctx.current_block);
         ctx.current_block = ctx.continue_target;

         if !linearize_block(ctx, bn, ast, target) {
            ctx.bbs[ctx.current_block]
               .instructions
               .push(CfgInstruction::Jump(ctx.continue_target));
            ctx.bbs[ctx.continue_target].predecessors.insert(ctx.current_block);
         }
         ctx.current_block = ctx.break_target;

         ctx.continue_target = old_cont_target;
         ctx.break_target = old_break_target;

         false
      }
      Statement::Break => {
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Jump(ctx.break_target));
         ctx.bbs[ctx.break_target].predecessors.insert(ctx.current_block);
         true
      }
      Statement::Continue => {
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Jump(ctx.continue_target));
         ctx.bbs[ctx.continue_target].predecessors.insert(ctx.current_block);
         true
      }
      Statement::Block(bn) => linearize_block(ctx, bn, ast, target),
      Statement::Return(e) => {
         ctx.bbs[ctx.current_block].instructions.push(CfgInstruction::Return(*e));
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Jump(CFG_END_NODE));
         ctx.bbs[CFG_END_NODE].predecessors.insert(ctx.current_block);
         true
      }
      Statement::Expression(e) => {
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Expression(*e));
         false
      }
      Statement::Assignment(lhs, rhs) => {
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Assignment(*lhs, *rhs));
         false
      }
      _ => unreachable!(),
   };
   ast.statements[stmt].statement = borrowed_stmt;

   sealed
}
