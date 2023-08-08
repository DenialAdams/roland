use std::collections::HashMap;

use bitvec::prelude::*;
use indexmap::{IndexMap, IndexSet};

use super::linearize::{Cfg, CfgInstruction};
use crate::backend::linearize::post_order;
use crate::parse::{AstPool, Expression, ExpressionId, Statement, StatementId, VariableId};
use crate::type_data::ExpressionType;

#[derive(Clone)]
struct LivenessState {
   live_in: BitBox,
   live_out: BitBox,
   gen: BitBox,
   kill: BitBox,
}

#[must_use]
pub fn liveness(
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &Cfg,
   ast: &AstPool,
) -> IndexMap<ProgramIndex, BitBox> {
   // Dataflow Analyis on the CFG
   let mut state = vec![
      LivenessState {
         live_in: bitbox![0; procedure_vars.len()],
         live_out: bitbox![0; procedure_vars.len()],
         gen: bitbox![0; procedure_vars.len()],
         kill: bitbox![0; procedure_vars.len()],
      };
      cfg.bbs.len()
   ];

   let var_to_dense: HashMap<VariableId, usize> = procedure_vars.keys().enumerate().map(|x| (*x.1, x.0)).collect();

   // Setup
   for (i, bb) in cfg.bbs.iter().enumerate() {
      let s = &mut state[i];
      for instruction in bb.instructions.iter().rev() {
         match instruction {
            CfgInstruction::RolandStmt(stmt) => {
               gen_kill_for_stmt(*stmt, &mut s.gen, &mut s.kill, ast, &var_to_dense);
            }
            CfgInstruction::ConditionalJump(expr, _, _) => {
               gen_for_expr(*expr, &mut s.gen, &mut s.kill, ast, &var_to_dense);
            }
            CfgInstruction::Jump(_) => (),
         }
      }
   }

   let mut worklist: IndexSet<usize> = post_order(cfg).into_iter().rev().collect();
   while let Some(node_id) = worklist.pop() {
      // TODO: There is a lot of cloning and creating new bitboxes in here that we probably don't need

      // Update live_out
      {
         let mut new_live_out = bitbox![0; procedure_vars.len()];
         for successor in cfg.bbs[node_id].successors() {
            let successor_s = &state[successor];
            new_live_out |= &successor_s.live_in;
         }

         state[node_id].live_out = new_live_out;
      }

      // Update live_in
      {
         let s = &mut state[node_id];
         let old_live_in = std::mem::replace(&mut s.live_in, bitbox![0; procedure_vars.len()]);
         s.live_in |= &s.gen;
         s.live_in |= s.live_out.clone() & !(s.kill.clone());

         if old_live_in != s.live_in {
            worklist.extend(&cfg.bbs[node_id].predecessors);
         }
      }
   }

   // Construct the final results
   let mut all_liveness: IndexMap<ProgramIndex, BitBox> = IndexMap::new();
   let node_id_to_rpo_index: HashMap<usize, usize> = post_order(cfg)
      .iter()
      .copied()
      .rev()
      .enumerate()
      .map(|(x, y)| (y, x))
      .collect();
   for (node_id, bb) in cfg.bbs.iter().enumerate() {
      // Nodes not present in the RPO are dead code, and so we will not mark them as having any live range
      let Some(rpo_index) = node_id_to_rpo_index.get(&node_id).copied() else {
         continue;
      };
      let s = &state[node_id];
      {
         let mut current_live_variables = s.live_out.clone();
         for (i, instruction) in bb.instructions.iter().enumerate().rev() {
            let pi = ProgramIndex(rpo_index, i);
            let var_to_kill = match instruction {
               CfgInstruction::RolandStmt(stmt) => {
                  update_live_variables_for_stmt(*stmt, &mut current_live_variables, ast, &var_to_dense)
               }
               CfgInstruction::ConditionalJump(expr, _, _) => {
                  update_live_variables_for_expr(*expr, &mut current_live_variables, ast, &var_to_dense);
                  None
               }
               CfgInstruction::Jump(_) => None,
            };
            all_liveness.insert(pi, current_live_variables.clone());
            if let Some(v) = var_to_kill {
               if let Some(di) = var_to_dense.get(&v).copied() {
                  current_live_variables.set(di, false);
               }
            }
         }
      }
   }

   all_liveness
}

fn update_live_variables_for_stmt(
   stmt: StatementId,
   current_live_variables: &mut BitBox,
   ast: &AstPool,
   var_to_dense: &HashMap<VariableId, usize>,
) -> Option<VariableId> {
   match &ast.statements[stmt].statement {
      Statement::Assignment(lhs, rhs) => {
         update_live_variables_for_expr(*rhs, current_live_variables, ast, var_to_dense);
         update_live_variables_for_expr(*lhs, current_live_variables, ast, var_to_dense);
         if let Expression::Variable(v) = ast.expressions[*lhs].expression {
            return Some(v);
         }
      }
      Statement::Expression(expr) => update_live_variables_for_expr(*expr, current_live_variables, ast, var_to_dense),
      Statement::Return(expr) => update_live_variables_for_expr(*expr, current_live_variables, ast, var_to_dense),
      _ => unreachable!(),
   }

   None
}

fn update_live_variables_for_expr(
   expr: ExpressionId,
   current_live_variables: &mut BitBox,
   ast: &AstPool,
   var_to_dense: &HashMap<VariableId, usize>,
) {
   match &ast.expressions[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         update_live_variables_for_expr(*proc_expr, current_live_variables, ast, var_to_dense);

         for val in args.iter().map(|x| x.expr) {
            update_live_variables_for_expr(val, current_live_variables, ast, var_to_dense);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            update_live_variables_for_expr(val, current_live_variables, ast, var_to_dense);
         }
      }
      Expression::ArrayIndex { array, index } => {
         update_live_variables_for_expr(*array, current_live_variables, ast, var_to_dense);
         update_live_variables_for_expr(*index, current_live_variables, ast, var_to_dense);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         update_live_variables_for_expr(*lhs, current_live_variables, ast, var_to_dense);
         update_live_variables_for_expr(*rhs, current_live_variables, ast, var_to_dense);
      }
      Expression::IfX(a, b, c) => {
         update_live_variables_for_expr(*a, current_live_variables, ast, var_to_dense);
         update_live_variables_for_expr(*b, current_live_variables, ast, var_to_dense);
         update_live_variables_for_expr(*c, current_live_variables, ast, var_to_dense);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            update_live_variables_for_expr(*expr, current_live_variables, ast, var_to_dense);
         }
      }
      Expression::FieldAccess(_, base_expr) => {
         update_live_variables_for_expr(*base_expr, current_live_variables, ast, var_to_dense);
      }
      Expression::Cast { expr, .. } => {
         update_live_variables_for_expr(*expr, current_live_variables, ast, var_to_dense);
      }
      Expression::UnaryOperator(_, expr) => {
         update_live_variables_for_expr(*expr, current_live_variables, ast, var_to_dense);
      }
      Expression::Variable(var) => {
         if let Some(di) = var_to_dense.get(var).copied() {
            current_live_variables.set(di, true);
         }
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

fn gen_kill_for_stmt(
   stmt: StatementId,
   gen: &mut BitBox,
   kill: &mut BitBox,
   ast: &AstPool,
   var_to_dense: &HashMap<VariableId, usize>,
) {
   match &ast.statements[stmt].statement {
      Statement::Assignment(lhs, rhs) => {
         gen_for_expr(*rhs, gen, kill, ast, var_to_dense);
         gen_for_expr(*lhs, gen, kill, ast, var_to_dense);
         if let Expression::Variable(v) = ast.expressions[*lhs].expression {
            if let Some(di) = var_to_dense.get(&v).copied() {
               gen.set(di, false);
               kill.set(di, true);
            }
         }
      }
      Statement::Expression(expr) => gen_for_expr(*expr, gen, kill, ast, var_to_dense),
      Statement::Return(expr) => gen_for_expr(*expr, gen, kill, ast, var_to_dense),
      _ => unreachable!(),
   }
}

fn gen_for_expr(
   expr: ExpressionId,
   gen: &mut BitBox,
   kill: &mut BitBox,
   ast: &AstPool,
   var_to_dense: &HashMap<VariableId, usize>,
) {
   match &ast.expressions[expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         gen_for_expr(*proc_expr, gen, kill, ast, var_to_dense);

         for val in args.iter().map(|x| x.expr) {
            gen_for_expr(val, gen, kill, ast, var_to_dense);
         }
      }
      Expression::ArrayLiteral(vals) => {
         for val in vals.iter().copied() {
            gen_for_expr(val, gen, kill, ast, var_to_dense);
         }
      }
      Expression::ArrayIndex { array, index } => {
         gen_for_expr(*array, gen, kill, ast, var_to_dense);
         gen_for_expr(*index, gen, kill, ast, var_to_dense);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         gen_for_expr(*lhs, gen, kill, ast, var_to_dense);
         gen_for_expr(*rhs, gen, kill, ast, var_to_dense);
      }
      Expression::IfX(a, b, c) => {
         gen_for_expr(*a, gen, kill, ast, var_to_dense);
         gen_for_expr(*b, gen, kill, ast, var_to_dense);
         gen_for_expr(*c, gen, kill, ast, var_to_dense);
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten() {
            gen_for_expr(*expr, gen, kill, ast, var_to_dense);
         }
      }
      Expression::FieldAccess(_, base_expr) => {
         gen_for_expr(*base_expr, gen, kill, ast, var_to_dense);
      }
      Expression::Cast { expr, .. } => {
         gen_for_expr(*expr, gen, kill, ast, var_to_dense);
      }
      Expression::UnaryOperator(_, expr) => {
         gen_for_expr(*expr, gen, kill, ast, var_to_dense);
      }
      Expression::Variable(var) => {
         if let Some(di) = var_to_dense.get(var).copied() {
            gen.set(di, true);
            kill.set(di, false);
         };
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
