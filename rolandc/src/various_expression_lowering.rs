use std::collections::HashMap;

use crate::parse::{Expression, ExpressionId, ExpressionPool, Program, VariableId};
use crate::typed_index_vec::Handle;

pub fn lower_single_expression(
   expressions: &mut ExpressionPool,
   expression_id: ExpressionId,
   const_replacements: &HashMap<VariableId, ExpressionId>,
) {
   match &expressions[expression_id].expression {
      Expression::Variable(x) => {
         if let Some(replacement_index) = const_replacements.get(x).copied() {
            expressions[expression_id].expression = expressions[replacement_index].expression.clone();
         }
      }
      Expression::UnresolvedVariable(_) => unreachable!(),
      _ => (),
   }
}

pub fn lower_consts(program: &mut Program, expressions: &mut ExpressionPool) {
   let mut const_replacements: HashMap<VariableId, ExpressionId> = HashMap::new();

   for p_const in program.consts.drain(..) {
      const_replacements.insert(p_const.var_id, p_const.value);
   }
   for i in 0..expressions.len() {
      lower_single_expression(expressions, ExpressionId::new(i), &const_replacements);
   }
}
