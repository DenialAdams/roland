use std::collections::HashMap;

use crate::backend::linearize::{post_order, Cfg, CfgInstruction};
use crate::expression_hoisting::is_reinterpretable_transmute;
use crate::parse::{CastType, Expression, ExpressionId, ExpressionPool, UnOp, VariableId};

#[derive(PartialEq, Clone, Copy)]
pub enum EscapingKind {
   MustLiveOnStackAlone,
   MustLiveOnStack,
}

pub fn mark_escaping_vars_cfg(cfg: &Cfg, escaping_vars: &mut HashMap<VariableId, EscapingKind>, ast: &ExpressionPool) {
   for bb in post_order(cfg) {
      for instr in cfg.bbs[bb].instructions.iter() {
         match instr {
            CfgInstruction::Assignment(lhs, rhs) => {
               mark_escaping_vars_expr(*lhs, escaping_vars, ast);
               mark_escaping_vars_expr(*rhs, escaping_vars, ast);
            }
            CfgInstruction::Expression(e)
            | CfgInstruction::ConditionalJump(e, _, _)
            | CfgInstruction::Return(e)
            | CfgInstruction::IfElse(e, _, _, _) => {
               mark_escaping_vars_expr(*e, escaping_vars, ast);
            }
            _ => (),
         }
      }
   }
}

fn mark_escaping_vars_expr(
   in_expr: ExpressionId,
   escaping_vars: &mut HashMap<VariableId, EscapingKind>,
   ast: &ExpressionPool,
) {
   match &ast[in_expr].expression {
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
               ast[*expr].exp_type.as_ref().unwrap(),
               ast[in_expr].exp_type.as_ref().unwrap(),
            )
         {
            if let Expression::Variable(v) = ast[*expr].expression {
               // Crucial here that we don't accidentally downgrade UnknownLifetime
               escaping_vars.entry(v).or_insert(EscapingKind::MustLiveOnStack);
            }
         }
      }
      Expression::UnaryOperator(op, expr) => {
         mark_escaping_vars_expr(*expr, escaping_vars, ast);
         if *op == UnOp::AddressOf {
            if let Expression::Variable(v) = ast[*expr].expression {
               escaping_vars.insert(v, EscapingKind::MustLiveOnStackAlone);
            }
         }
      }
      Expression::Variable(_)
      | Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::UnitLiteral
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_) => (),
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}
