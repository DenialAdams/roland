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
      Expression::IfX(a, b, c) => {
         *a = deep_clone_expr(*a, cloner);
         *b = deep_clone_expr(*b, cloner);
         *c = deep_clone_expr(*c, cloner);
      }
      Expression::ProcedureCall { proc_expr, args } => {
         *proc_expr = deep_clone_expr(*proc_expr, cloner);
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(arg.expr, cloner);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(*expr, cloner);
         }
      }
      Expression::Variable(x) => {
         *x = cloner.replacement_var(*x);
      }
      Expression::BinaryOperator { lhs: a, rhs: b, .. } | Expression::ArrayIndex { array: a, index: b } => {
         *a = deep_clone_expr(*a, cloner);
         *b = deep_clone_expr(*b, cloner);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, cloner);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.values_mut().flatten() {
            *field_expr = deep_clone_expr(*field_expr, cloner);
         }
      }
      Expression::UnresolvedStructLiteral(_, field_exprs, _) => {
         for field_expr in field_exprs.iter_mut().flat_map(|x| &mut x.1) {
            *field_expr = deep_clone_expr(*field_expr, cloner);
         }
      }
      Expression::FieldAccess(_, expr) | Expression::Cast { expr, .. } => {
         *expr = deep_clone_expr(*expr, cloner);
      }
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedEnumLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral
      | Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _) => (),
   }
   cloner.dst_pool().insert(cloned_expr)
}
