use crate::interner::StrId;
use crate::parse::{Expression, Program, ExpressionIndex};
use std::collections::HashMap;
use std::io::Write;

pub fn lower_consts<W: Write>(program: &mut Program, err_stream: &mut W) {
   let mut const_replacements: HashMap<StrId, ExpressionIndex> = HashMap::new();

   for p_const in program.consts.drain(0..) {
      const_replacements.insert(p_const.name.identifier, p_const.value);
   }

   for en in program.expressions.iter_mut() {
      let var_name = match en.expression {
        Expression::Variable(x) => Some(x),
        _ => None
      };

      if let Some(replacement_index) = var_name.as_ref().and_then(|x| const_replacements.get(x)) {
         en.expression = program.expressions[replacement_index.0].expression;
      }
   }
}
