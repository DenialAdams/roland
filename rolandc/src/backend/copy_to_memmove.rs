use std::collections::HashMap;

use crate::BaseTarget;
use crate::backend::linearize::{CfgInstruction, post_order};
use crate::backend::pointer_analysis::PointerAnalysisResult;
use crate::interner::{Interner, StrId};
use crate::parse::{
   ArgumentNode, Expression, ExpressionId, ExpressionNode, ExpressionPool, ProcedureBody, ProcedureId, UnOp,
   UserDefinedTypeInfo, VariableId,
};
use crate::size_info::sizeof_type_mem;
use crate::type_data::{ExpressionType, U64_TYPE};

fn get_mem_var(expr: ExpressionId, ast: &ExpressionPool, is_lhs: bool) -> Option<(bool, VariableId)> {
   match ast[expr].expression {
      Expression::Variable(v) if is_lhs => Some((false, v)),
      Expression::UnaryOperator(UnOp::Dereference, e) if is_lhs => {
         let Expression::Variable(v) = ast[e].expression else {
            unreachable!()
         };
         Some((true, v))
      }
      Expression::UnaryOperator(UnOp::Dereference, e) => get_mem_var(e, ast, true),
      _ => None,
   }
}

pub fn lower_overlapping_copies_to_memmove(
   pointer_analysis_results: &PointerAnalysisResult,
   body: &mut ProcedureBody,
   procedure_name_table: &HashMap<StrId, ProcedureId>,
   udt: &UserDefinedTypeInfo,
   interner: &Interner,
) {
   let proc_id = procedure_name_table[&interner.reverse_lookup("_roland_memmove_bytes").unwrap()];
   for bb in post_order(&body.cfg).iter() {
      for instr in body.cfg.bbs[*bb].instructions.iter_mut() {
         let CfgInstruction::Assignment(lhs, rhs) = instr else {
            continue;
         };
         let lhs = *lhs;
         let rhs = *rhs;
         if !body.ast.expressions[rhs].exp_type.as_ref().unwrap().is_aggregate() {
            continue;
         }
         let Some((lhs_is_indirect, lhs_var)) = get_mem_var(lhs, &body.ast.expressions, true) else {
            continue;
         };
         let Some((rhs_is_indirect, rhs_var)) = get_mem_var(rhs, &body.ast.expressions, false) else {
            continue;
         };
         let may_overlap = 'alias: {
            let Some(lhs_var_local_idx) = body.locals.get_index_of(&lhs_var) else {
               break 'alias true;
            };
            let Some(rhs_var_local_idx) = body.locals.get_index_of(&rhs_var) else {
               break 'alias true;
            };

            match (lhs_is_indirect, rhs_is_indirect) {
               (false, false) => false,
               (false, true) => pointer_analysis_results.may_point_to(rhs_var_local_idx, lhs_var_local_idx),
               (true, false) => pointer_analysis_results.may_point_to(lhs_var_local_idx, rhs_var_local_idx),
               (true, true) => pointer_analysis_results.may_alias(lhs_var_local_idx, rhs_var_local_idx),
            }
         };
         if !may_overlap {
            continue;
         }
         {
            let location = body.block.location; // dummy, to be improved when we track locations on CfgInstructions
            let proc_expr = body.ast.expressions.insert(ExpressionNode {
               expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
               exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
               location,
            });
            let size = sizeof_type_mem(
               body.ast.expressions[rhs].exp_type.as_ref().unwrap(),
               udt,
               BaseTarget::Qbe,
            );
            let Expression::UnaryOperator(UnOp::Dereference, rhs_stripped) = body.ast.expressions[rhs].expression
            else {
               unreachable!()
            };
            let size_arg = body.ast.expressions.insert(ExpressionNode {
               expression: Expression::IntLiteral {
                  val: size,
                  synthetic: true,
               },
               exp_type: Some(U64_TYPE),
               location,
            });
            let new_call = body.ast.expressions.insert(ExpressionNode {
               exp_type: Some(ExpressionType::Unit),
               expression: Expression::ProcedureCall {
                  proc_expr,
                  args: vec![
                     ArgumentNode { expr: lhs, name: None },
                     ArgumentNode {
                        expr: rhs_stripped,
                        name: None,
                     },
                     ArgumentNode {
                        expr: size_arg,
                        name: None,
                     },
                  ]
                  .into_boxed_slice(),
               },
               location,
            });
            *instr = CfgInstruction::Expression(new_call);

            // Adjust the types to match the call (lowered pointers)
            body.ast.expressions[lhs].exp_type = Some(U64_TYPE);
            body.ast.expressions[rhs_stripped].exp_type = Some(U64_TYPE);
         }
      }
   }
}
