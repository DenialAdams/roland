use crate::parse::{Expression, ExpressionId, ExpressionPool, VariableId};

pub trait Cloner {
   fn replacement_var(&self, v: VariableId) -> VariableId;
   fn src_pool(&self) -> &ExpressionPool;
   fn dst_pool(&mut self) -> &mut ExpressionPool;
}

#[must_use]
pub fn deep_clone_expr<C: Cloner>(expr: ExpressionId, cloner: &mut C) -> ExpressionId {
   let mut cloned_expr = cloner.src_pool()[expr].clone();
   match &mut cloned_expr.expression {
      Expression::Variable(var) => *var = cloner.replacement_var(*var),
      expr => expr.for_each_child_mut(|child| *child = deep_clone_expr(*child, cloner)),
   }
   cloner.dst_pool().insert(cloned_expr)
}
