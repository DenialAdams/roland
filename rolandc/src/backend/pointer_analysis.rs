use std::collections::HashMap;

use bitvec::bitbox;
use bitvec::boxed::BitBox;
use bitvec::slice::BitSlice;
use indexmap::IndexMap;

use crate::backend::linearize::{Cfg, CfgInstruction, post_order};
use crate::disjoint_set::DisjointSet;
use crate::parse::{BinOp, Expression, ExpressionId, ExpressionPool, UnOp, VariableId};
use crate::type_data::ExpressionType;

pub struct PointerAnalysisResult {
   ds: DisjointSet,
   reverse_points_to: HashMap<usize, WhoPointsToOwned>,
}

pub enum WhoPointsToOwned {
   Unknown,
   Vars(BitBox),
}

impl WhoPointsToOwned {
   pub fn as_ref(&self) -> WhoPointsTo<'_> {
      match self {
         WhoPointsToOwned::Unknown => WhoPointsTo::Unknown,
         WhoPointsToOwned::Vars(bb) => WhoPointsTo::Vars(bb.as_bitslice()),
      }
   }
}

pub enum WhoPointsTo<'a> {
   Unknown,
   Vars(&'a BitSlice),
}

impl PointerAnalysisResult {
   pub fn who_points_to(&self, x: usize) -> WhoPointsTo<'_> {
      self
         .reverse_points_to
         .get(&self.ds.find(x))
         .map_or(WhoPointsTo::Vars(BitSlice::empty()), |x| x.as_ref())
   }
}

struct PointerAnalysisData {
   ds: DisjointSet,
   points_to: HashMap<usize, usize>,
   unknown: usize,
}

impl PointerAnalysisData {
   fn join(&mut self, x: usize, y: usize) {
      let rx = self.ds.find(x);
      let ry = self.ds.find(y);

      if rx == ry {
         return;
      }

      self.ds.union(rx, ry);
      let new_rep = self.ds.find(rx);

      let x_target = self.points_to.get(&rx).copied().map(|t| self.ds.find(t));
      let y_target = self.points_to.get(&ry).copied().map(|t| self.ds.find(t));
      match (x_target, y_target) {
         (None, None) => (),
         (None, Some(t)) | (Some(t), None) => {
            self.points_to.insert(new_rep, self.ds.find(t));
         }
         (Some(t1), Some(t2)) => {
            self.join(t1, t2);
            self.points_to.insert(new_rep, self.ds.find(t1));
         }
      }
   }

   fn add_points_to(&mut self, x: usize, target: usize) {
      let x = self.ds.find(x);
      let target = self.ds.find(target);
      if let Some(old_val) = self.points_to.insert(x, target) {
         self.join(old_val, target);
      }
   }

   fn add_unknown_points_to(&mut self, x: usize) {
      self.add_points_to(self.unknown, x);
   }

   fn build_result(self, procedure_vars: &IndexMap<VariableId, ExpressionType>) -> PointerAnalysisResult {
      let mut reverse_points_to: HashMap<usize, WhoPointsToOwned> = HashMap::new();
      // Unknown
      {
         let rep = self.ds.find(self.unknown);
         if let Some(rep_points_to) = self.points_to.get(&rep).map(|x| self.ds.find(*x)) {
            reverse_points_to.insert(rep_points_to, WhoPointsToOwned::Unknown);
         }
      }
      for i in 0..procedure_vars.len() {
         let rep = self.ds.find(i);
         let Some(rep_points_to) = self.points_to.get(&rep).map(|x| self.ds.find(*x)) else {
            continue;
         };
         match reverse_points_to
            .entry(rep_points_to)
            .or_insert(WhoPointsToOwned::Vars(bitbox![0; procedure_vars.len()]))
         {
            WhoPointsToOwned::Unknown => (),
            WhoPointsToOwned::Vars(bit_vec) => {
               bit_vec.set(i, true);
            }
         }
      }
      PointerAnalysisResult {
         reverse_points_to,
         ds: self.ds,
      }
   }
}

// Conservative, flow-insensitive pointer information
pub fn steensgard(
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
   cfg: &mut Cfg,
   ast: &ExpressionPool,
) -> PointerAnalysisResult {
   let mut data = {
      let mut ds = DisjointSet::new();
      for _ in procedure_vars.iter() {
         ds.add_new_set();
      }
      let unknown = ds.add_new_set();
      PointerAnalysisData {
         ds,
         points_to: HashMap::new(),
         unknown,
      }
   };
   for bb_index in post_order(cfg) {
      let bb = &cfg.bbs[bb_index];
      for instr in bb.instructions.iter() {
         match instr {
            CfgInstruction::Assignment(lhs, rhs) => {
               let lhs_di = address_node_escaping_from_expr(*lhs, &mut data, ast, procedure_vars);
               let rhs_di = address_node_escaping_from_expr(*rhs, &mut data, ast, procedure_vars);
               match (lhs_di, rhs_di) {
                  (_, None) => (),
                  (None, Some(r)) => {
                     // something like (0xdeadbeef as &u8)~ = &x;
                     data.add_unknown_points_to(r);
                  }
                  (Some(l), Some(r)) => {
                     data.add_points_to(l, r);
                  }
               }
            }
            CfgInstruction::Expression(expr)
            | CfgInstruction::Return(expr)
            | CfgInstruction::ConditionalJump(expr, _, _) => {
               address_node_escaping_from_expr(*expr, &mut data, ast, procedure_vars);
            }
            CfgInstruction::Nop | CfgInstruction::Jump(_) => (),
         }
      }
   }

   data.build_result(procedure_vars)
}

fn address_node_escaping_from_expr(
   in_expr: ExpressionId,
   data: &mut PointerAnalysisData,
   ast: &ExpressionPool,
   procedure_vars: &IndexMap<VariableId, ExpressionType>,
) -> Option<usize> {
   match &ast[in_expr].expression {
      Expression::ProcedureCall { proc_expr, args } => {
         address_node_escaping_from_expr(*proc_expr, data, ast, procedure_vars);

         for val in args.iter().map(|x| x.expr) {
            if let Some(di) = address_node_escaping_from_expr(val, data, ast, procedure_vars) {
               // The caller could store the address into a global or write through it
               data.add_unknown_points_to(di);
               data.add_points_to(di, data.unknown);
            }
         }

         // Could have returned an address
         Some(data.unknown)
      }
      Expression::BinaryOperator { lhs, rhs, operator } => {
         let a = address_node_escaping_from_expr(*lhs, data, ast, procedure_vars);
         let b = address_node_escaping_from_expr(*rhs, data, ast, procedure_vars);

         match operator {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::Remainder
            | BinOp::BitwiseAnd
            | BinOp::BitwiseOr
            | BinOp::BitwiseXor
            | BinOp::BitwiseLeftShift
            | BinOp::BitwiseRightShift => (),
            BinOp::Equality
            | BinOp::NotEquality
            | BinOp::GreaterThan
            | BinOp::LessThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThanOrEqualTo
            | BinOp::LogicalAnd
            | BinOp::LogicalOr => return None,
         }

         if let Some(di_a) = a
            && let Some(di_b) = b
         {
            // a strange case like &a + &b
            data.join(di_a, di_b);
         }

         a.or(b)
      }
      Expression::IfX(a, b, c) => {
         address_node_escaping_from_expr(*a, data, ast, procedure_vars);
         let eb = address_node_escaping_from_expr(*b, data, ast, procedure_vars);
         let ec = address_node_escaping_from_expr(*c, data, ast, procedure_vars);

         if let Some(dib) = eb
            && let Some(dic) = ec
         {
            data.join(dib, dic);
         }

         eb.or(ec)
      }
      Expression::UnaryOperator(UnOp::Dereference, expr) => {
         let derefd_item = address_node_escaping_from_expr(*expr, data, ast, procedure_vars);
         derefd_item
            .map(|i| {
               data
                  .points_to
                  .entry(data.ds.find(i))
                  .or_insert_with(|| data.ds.add_new_set())
            })
            .copied()
            .map(|i| data.ds.find(i))
      }
      Expression::Cast { expr, .. } | Expression::UnaryOperator(_, expr) => {
         address_node_escaping_from_expr(*expr, data, ast, procedure_vars)
      }
      Expression::Variable(v) => procedure_vars.get_index_of(v).or(Some(data.unknown)),
      Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => None,
      Expression::ArrayIndex { .. }
      | Expression::FieldAccess(_, _)
      | Expression::ArrayLiteral(_)
      | Expression::StructLiteral(_, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}
