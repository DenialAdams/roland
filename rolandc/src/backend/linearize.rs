use std::collections::HashSet;

use arrayvec::ArrayVec;
use slotmap::SecondaryMap;

use crate::interner::Interner;
use crate::parse::{
   AstPool, BlockNode, ExpressionId, ProcImplSource, ProcedureId, Statement, StatementId, StatementNode,
};
use crate::Program;

// TODO: This is pretty bulky. Ideally this would be size <= 8 for storage in the BB.
pub enum CfgInstruction {
   RolandStmt(StatementId),
   ConditionalJump(ExpressionId, usize, usize),
   Jump(usize),
}

pub struct BasicBlock {
   pub instructions: Vec<CfgInstruction>,
   pub predecessors: HashSet<usize>,
}

impl BasicBlock {
   fn successors(&self) -> ArrayVec<usize, 2> {
      let mut buf = ArrayVec::new();
      if let Some(x) = self.instructions.last() {
         match x {
            CfgInstruction::RolandStmt(_) => {}
            CfgInstruction::ConditionalJump(_, a, b) => {
               buf.push(*a);
               buf.push(*b);
            }
            CfgInstruction::Jump(x) => {
               buf.push(*x);
            }
         }
      }

      buf
   }
}

struct Ctx {
   bbs: Vec<BasicBlock>,
   current_block: usize,
   break_target: usize,
   continue_target: usize,
}

fn simplify_cfg(cfg: &mut [BasicBlock], ast: &mut AstPool) {
   // TODO: this simplification will not remove the starting basic block, even when it could
   // (but maybe we always want a start and end basic block in the long term anyway)
   // TODO: can we do this without the outer loop?
   let mut did_something = true;
   while did_something {
      did_something = false;

      for node in 0..cfg.len() {
         if cfg[node].instructions.len() != 1 || cfg[node].predecessors.is_empty() {
            continue;
         }

         let dest = if let Some(CfgInstruction::Jump(dest)) = cfg[node].instructions.last() {
            *dest
         } else {
            continue;
         };

         let preds = std::mem::take(&mut cfg[node].predecessors);
         for pred in preds {
            if pred == node {
               cfg[node].predecessors.insert(pred);
               continue;
            }
            did_something = true;
            let mut new_jump = None;
            let last_in_pred = cfg[pred].instructions.last_mut().unwrap();
            match last_in_pred {
               CfgInstruction::RolandStmt(_) => unreachable!(),
               CfgInstruction::ConditionalJump(cond_expr, x, y) => {
                  if *x == node {
                     *x = dest;
                  } else {
                     debug_assert!(*y == node);
                     *y = dest;
                  }
                  if *x == *y {
                     // We do NOT skip doing this even if the expression doesn't have side effects
                     // That's because as of the time of writing, this CFG does not replace the AST, it just lives next to it
                     // I don't want the CFG to mismatch the AST, even in a semantic preserving way,
                     // because we are going to generate code from this AST naively and so if we delete a use that impacts register allocation
                     // something bad could happen or something. In the long term, we want the CFG generation to be a real thing in the compiler pipeline
                     // that can do whatever it wants.
                     let cond_stmt = ast.statements.insert(StatementNode {
                        statement: Statement::Expression(*cond_expr),
                        location: ast.expressions[*cond_expr].location,
                     });
                     new_jump = Some(*x);
                     *last_in_pred = CfgInstruction::RolandStmt(cond_stmt);
                  }
               }
               CfgInstruction::Jump(x) => {
                  debug_assert!(*x == node);
                  *x = dest;
               }
            }
            if let Some(target) = new_jump {
               cfg[pred].instructions.push(CfgInstruction::Jump(target));
            }
            cfg[dest].predecessors.insert(pred);
         }
      }
   }
}

fn dump_program_cfg(all_cfg: &ProgramCfg, interner: &Interner, program: &Program) {
   let mut f = std::fs::File::create("cfg.dot").unwrap();
   for (proc, cfg) in all_cfg.iter() {
      use std::io::Write;
      writeln!(
         f,
         "digraph {} {{",
         interner.lookup(program.procedures[proc].definition.name.str)
      )
      .unwrap();
      for node in post_order(cfg) {
         let successors = cfg[node].successors();
         for succ in successors.iter() {
            writeln!(f, "\"{}\" -> \"{}\"", bb_id_to_label(node), bb_id_to_label(*succ)).unwrap();
         }
         if successors.is_empty() {
            writeln!(f, "\"{}\"", bb_id_to_label(node)).unwrap();
         }
      }
      writeln!(f, "}}").unwrap();
   }
}

pub type ProgramCfg = SecondaryMap<ProcedureId, Vec<BasicBlock>>;

pub fn linearize(program: &mut Program, interner: &Interner) -> ProgramCfg {
   let mut ctx = Ctx {
      bbs: vec![],
      current_block: 0,
      break_target: 0,
      continue_target: 0,
   };
   let mut all_cfg: SecondaryMap<ProcedureId, Vec<BasicBlock>> = SecondaryMap::new();
   for proc in program.procedures.iter() {
      let ProcImplSource::Body(body) = &proc.1.proc_impl else {
         continue;
      };

      ctx.bbs.push(BasicBlock {
         instructions: vec![],
         predecessors: HashSet::new(),
      });
      ctx.current_block = 0;

      let _ = linearize_block(&mut ctx, body, &program.ast);

      simplify_cfg(&mut ctx.bbs, &mut program.ast);

      all_cfg.insert(proc.0, std::mem::take(&mut ctx.bbs));
   }

   dump_program_cfg(&all_cfg, interner, program);

   all_cfg
}

fn bb_id_to_label(bb_id: usize) -> String {
   let tformed = (bb_id + 65) as u8 as char;
   if tformed == '\\' {
      String::from("\\\\")
   } else {
      String::from(tformed)
   }
}

fn post_order(cfg: &[BasicBlock]) -> Vec<usize> {
   let mut visited = HashSet::new();
   let mut post_order = vec![];
   dfs(cfg, 0, &mut visited, &mut post_order);
   post_order
}

fn dfs(cfg: &[BasicBlock], node: usize, visited: &mut HashSet<usize>, post_order: &mut Vec<usize>) {
   let successors = cfg[node].successors();

   visited.insert(node);
   for succ in successors {
      if !visited.contains(&succ) {
         dfs(cfg, succ, visited, post_order);
      }
   }

   post_order.push(node);
}

#[must_use]
fn linearize_block(ctx: &mut Ctx, block: &BlockNode, ast: &AstPool) -> bool {
   for stmt in block.statements.iter() {
      if linearize_stmt(ctx, *stmt, ast) {
         return true;
      }
   }

   false
}

#[must_use]
fn linearize_stmt(ctx: &mut Ctx, stmt: StatementId, ast: &AstPool) -> bool {
   match &ast.statements[stmt].statement {
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
         if !linearize_block(ctx, consequent, ast) {
            ctx.bbs[ctx.current_block]
               .instructions
               .push(CfgInstruction::Jump(afterwards_dest));
            ctx.bbs[afterwards_dest].predecessors.insert(ctx.current_block);
         }

         ctx.current_block = else_dest;
         if !linearize_stmt(ctx, *alternative, ast) {
            ctx.bbs[ctx.current_block]
               .instructions
               .push(CfgInstruction::Jump(afterwards_dest));
            ctx.bbs[afterwards_dest].predecessors.insert(ctx.current_block);
         }

         ctx.current_block = afterwards_dest;
         // TODO: push region labels?
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

         if !linearize_block(ctx, bn, ast) {
            ctx.bbs[ctx.current_block]
               .instructions
               .push(CfgInstruction::Jump(ctx.continue_target));
            ctx.bbs[ctx.continue_target].predecessors.insert(ctx.current_block);
         }
         ctx.current_block = ctx.break_target;

         ctx.continue_target = old_cont_target;
         ctx.break_target = old_break_target;
      }
      Statement::Break => {
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Jump(ctx.break_target));
         ctx.bbs[ctx.break_target].predecessors.insert(ctx.current_block);
         return true;
      }
      Statement::Continue => {
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::Jump(ctx.continue_target));
         ctx.bbs[ctx.break_target].predecessors.insert(ctx.continue_target);
         return true;
      }
      Statement::Block(bn) => {
         if linearize_block(ctx, bn, ast) {
            return true;
         }
      }
      _ => {
         // Note that return statements do not (currently) influence the CFG.
         ctx.bbs[ctx.current_block]
            .instructions
            .push(CfgInstruction::RolandStmt(stmt));
      }
   }

   false
}
