use crate::interner::StrId;
use crate::parse::{Expression, ExpressionIndex, ExpressionNode, Program};
use crate::typed_index_vec::{Handle, HandleMap};
use std::collections::HashMap;

pub fn lower_consts(program: &mut Program, expressions: &mut HandleMap<ExpressionIndex, ExpressionNode>) {
   let mut const_replacements: HashMap<StrId, ExpressionIndex> = HashMap::new();

   for p_const in program.consts.drain(0..) {
      const_replacements.insert(p_const.name.identifier, p_const.value);
   }

   for i in 0..expressions.len() {
      let var_name = match expressions[ExpressionIndex::new(i)].expression {
         Expression::Variable(x) => Some(x),
         _ => None,
      };

      if let Some(replacement_index) = var_name.as_ref().and_then(|x| const_replacements.get(x)).copied() {
         expressions[ExpressionIndex::new(i)].expression = expressions[replacement_index].expression.clone();
      }
   }
}
