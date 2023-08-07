use std::collections::{HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};

use super::linearize::{Cfg, CFG_END_NODE};
use crate::backend::linearize::post_order;
use crate::parse::{AstPool, Expression, ExpressionId, Statement, StatementId, VariableId};

fn choose_from_worklist(w: &mut IndexSet<usize>) -> Option<usize> {
   if w.contains(&CFG_END_NODE) {
      w.remove(&CFG_END_NODE);
      return Some(CFG_END_NODE);
   }

   w.pop()
}

// TODO: bitsets. related, we shouldn't use VariableIds as bitset key,
// but instead the index into the procedure.locals variable table corresponding
// to that VariableId (so that the bitset key is dense.)
#[derive(Clone)]
struct LivenessState {
   live_in: HashSet<VariableId>,  //TODO: bitset
   live_out: HashSet<VariableId>, //TODO: bitset
   gen: HashSet<VariableId>,      //TODO: bitset
   kill: HashSet<VariableId>,     //TODO: bitset
}

#[must_use]
pub fn liveness(cfg: &Cfg, ast: &AstPool) -> IndexMap<ProgramIndex, HashSet<VariableId>> {
   // We will:
   //   1) Perform dataflow analysis on the CFG
   //   2) Propagate the final result locally within basic blocks
   //   3) Prepare and return a mapping of variables to their live interval
   // At some point we may want to factor 3 out, since we only need that for linear scan,
   // and then we can have the option for graph coloring

   // Dataflow Analyis on the CFG
   let mut state = vec![
      LivenessState {
         live_in: HashSet::new(),
         live_out: HashSet::new(),
         gen: HashSet::new(),
         kill: HashSet::new()
      };
      cfg.bbs.len()
   ];
   // Setup
   for (i, bb) in cfg.bbs.iter().enumerate() {
      let s = &mut state[i];
      for instruction in bb.instructions.iter().rev() {
         match instruction {
            super::linearize::CfgInstruction::RolandStmt(stmt) => {
               gen_kill_for_stmt(*stmt, &mut s.gen, &mut s.kill, ast);
            }
            super::linearize::CfgInstruction::ConditionalJump(_, _, _) => (),
            super::linearize::CfgInstruction::Jump(_) => (),
         }
      }
   }

   let mut worklist: IndexSet<usize> = post_order(cfg).into_iter().collect();
   while let Some(node_id) = choose_from_worklist(&mut worklist) {
      let s = &mut state[node_id];
      let old_live_in = std::mem::take(&mut s.live_in);
      s.live_in.extend(&s.gen);
      s.live_in.extend(s.live_out.difference(&s.kill));

      if old_live_in != s.live_in {
         worklist.extend(&cfg.bbs[node_id].predecessors);
      }

      let mut new_live_out = std::mem::take(&mut s.live_out);
      new_live_out.clear();
      for successor in cfg.bbs[node_id].successors() {
         let successor_s = &state[successor];
         new_live_out.extend(&successor_s.live_in);
      }

      let s = &mut state[node_id];
      s.live_out = new_live_out;
   }

   // Construct the final results
   let mut all_liveness: IndexMap<ProgramIndex, HashSet<VariableId>> = IndexMap::new();
   let node_id_to_rpo_index: HashMap<usize, usize> = post_order(cfg).iter().copied().rev().enumerate().map(|(x, y)| (y, x)).collect();
   for (node_id, bb) in cfg.bbs.iter().enumerate() {
      // Nodes not present in the RPO are dead code, and so we will not mark them as having any live range
      let Some(rpo_index) = node_id_to_rpo_index.get(&node_id).copied() else { continue; };
      let s = &state[node_id];
      {
         let mut current_live_variables = s.live_out.clone();
         for (i, instruction) in bb.instructions.iter().enumerate().rev() {
            let pi = ProgramIndex(rpo_index, i);
            let var_to_kill = match instruction {
               super::linearize::CfgInstruction::RolandStmt(stmt) => {
                  update_live_variables_for_stmt(*stmt, &mut current_live_variables, ast)
               }
               super::linearize::CfgInstruction::ConditionalJump(_, _, _) => None,
               super::linearize::CfgInstruction::Jump(_) => None,
            };
            all_liveness.insert(pi, current_live_variables.clone());
            if let Some(v) = var_to_kill {
               current_live_variables.remove(&v);
            }
         }
      }
   }

   all_liveness
}

fn update_live_variables_for_stmt(stmt: StatementId, current_live_variables: &mut HashSet<VariableId>, ast: &AstPool) -> Option<VariableId> {
   match &ast.statements[stmt].statement {
      Statement::Assignment(lhs, rhs) => {
         update_live_variables_for_expr(*rhs, current_live_variables, ast);
         update_live_variables_for_expr(*lhs, current_live_variables, ast);
         if let Expression::Variable(v) = ast.expressions[*lhs].expression {
            return Some(v);
         }
      }
      Statement::Expression(expr) => update_live_variables_for_expr(*expr, current_live_variables, ast),
      Statement::Return(expr) => update_live_variables_for_expr(*expr, current_live_variables, ast),
      _ => unreachable!(),
   }

   None
}

fn update_live_variables_for_expr(expr: ExpressionId, current_live_variables: &mut HashSet<VariableId>, ast: &AstPool) {
   match &ast.expressions[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         update_live_variables_for_expr(*proc_expr, current_live_variables, ast);

         for val in args.iter().map(|x| x.expr) {
            update_live_variables_for_expr(val, current_live_variables, ast);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            update_live_variables_for_expr(val, current_live_variables, ast);
         }
      }
      Expression::ArrayIndex { array, index } => {
         update_live_variables_for_expr(*array, current_live_variables, ast);
         update_live_variables_for_expr(*index, current_live_variables, ast);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         update_live_variables_for_expr(*lhs, current_live_variables, ast);
         update_live_variables_for_expr(*rhs, current_live_variables, ast);
      }
      Expression::IfX(a, b, c) => {
         update_live_variables_for_expr(*a, current_live_variables, ast);
         update_live_variables_for_expr(*b, current_live_variables, ast);
         update_live_variables_for_expr(*c, current_live_variables, ast);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            update_live_variables_for_expr(*expr, current_live_variables, ast);
         }
      }
      Expression::FieldAccess(_, base_expr) => {
         update_live_variables_for_expr(*base_expr, current_live_variables, ast);
      }
      Expression::Cast { expr, .. } => {
         update_live_variables_for_expr(*expr, current_live_variables, ast);
      }
      Expression::UnaryOperator(_, expr) => {
         update_live_variables_for_expr(*expr, current_live_variables, ast);
      }
      Expression::Variable(var) => {
         current_live_variables.insert(*var);
      }
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

fn gen_kill_for_stmt(stmt: StatementId, gen: &mut HashSet<VariableId>, kill: &mut HashSet<VariableId>, ast: &AstPool) {
   match &ast.statements[stmt].statement {
      Statement::Assignment(lhs, rhs) => {
         gen_for_expr(*rhs, gen, kill, ast);
         gen_for_expr(*lhs, gen, kill, ast);
         if let Expression::Variable(v) = ast.expressions[*lhs].expression {
            gen.remove(&v);
            kill.insert(v);
         }
      }
      Statement::Expression(expr) => gen_for_expr(*expr, gen, kill, ast),
      Statement::Return(expr) => gen_for_expr(*expr, gen, kill, ast),
      _ => unreachable!(),
   }
}

fn gen_for_expr(expr: ExpressionId, gen: &mut HashSet<VariableId>, kill: &mut HashSet<VariableId>, ast: &AstPool) {
   match &ast.expressions[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         gen_for_expr(*proc_expr, gen, kill, ast);

         for val in args.iter().map(|x| x.expr) {
            gen_for_expr(val, gen, kill, ast);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            gen_for_expr(val, gen, kill, ast);
         }
      }
      Expression::ArrayIndex { array, index } => {
         gen_for_expr(*array, gen, kill, ast);
         gen_for_expr(*index, gen, kill, ast);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         gen_for_expr(*lhs, gen, kill, ast);
         gen_for_expr(*rhs, gen, kill, ast);
      }
      Expression::IfX(a, b, c) => {
         gen_for_expr(*a, gen, kill, ast);
         gen_for_expr(*b, gen, kill, ast);
         gen_for_expr(*c, gen, kill, ast);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            gen_for_expr(*expr, gen, kill, ast);
         }
      }
      Expression::FieldAccess(_, base_expr) => {
         gen_for_expr(*base_expr, gen, kill, ast);
      }
      Expression::Cast { expr, .. } => {
         gen_for_expr(*expr, gen, kill, ast);
      }
      Expression::UnaryOperator(_, expr) => {
         gen_for_expr(*expr, gen, kill, ast);
      }
      Expression::Variable(var) => {
         gen.insert(*var);
         kill.remove(var);
      }
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

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProgramIndex(pub usize, pub usize); // (RPO basic block position, instruction inside of block)
