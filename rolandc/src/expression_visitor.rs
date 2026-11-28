use crate::parse::{Expression, ExpressionId};

impl Expression {
   #[inline]
   pub(crate) fn for_each_child_assuming_resolved(&self, mut visit: impl FnMut(ExpressionId)) {
      self.all_children_assuming_resolved(|child| {
         visit(child);
         true
      });
   }

   #[inline]
   pub(crate) fn all_children_assuming_resolved(&self, mut test: impl FnMut(ExpressionId) -> bool) -> bool {
      match self {
         Self::ProcedureCall { proc_expr, args } => test(*proc_expr) && args.iter().all(|arg| test(arg.expr)),
         Self::ArrayLiteral(children) => children.iter().copied().all(test),
         Self::ArrayIndex { array: lhs, index: rhs } | Self::BinaryOperator { lhs, rhs, .. } => {
            test(*lhs) && test(*rhs)
         }
         Self::IfX(cond, then_expr, else_expr) => test(*cond) && test(*then_expr) && test(*else_expr),
         Self::UnaryOperator(_, child) | Self::FieldAccess(_, child) | Self::Cast { expr: child, .. } => test(*child),
         Self::StructLiteral(_, fields) => {
            for child in fields.values().flatten().copied() {
               if !test(child) {
                  return false;
               }
            }
            true
         }
         Self::BoolLiteral(_)
         | Self::StringLiteral(_)
         | Self::IntLiteral { .. }
         | Self::FloatLiteral(_)
         | Self::UnitLiteral
         | Self::Variable(_)
         | Self::EnumLiteral(_, _)
         | Self::BoundFcnLiteral(_, _) => true,
         Self::UnresolvedStructLiteral(_, _, _)
         | Self::UnresolvedVariable(_)
         | Self::UnresolvedEnumLiteral(_, _)
         | Self::UnresolvedProcLiteral(_, _) => unreachable!("read-only child visitor requires a resolved expression"),
      }
   }

   #[inline]
   pub(crate) fn for_each_child_mut(&mut self, mut visit: impl FnMut(&mut ExpressionId)) {
      match self {
         Self::ProcedureCall { proc_expr, args } => {
            visit(proc_expr);
            for arg in args {
               visit(&mut arg.expr);
            }
         }
         Self::ArrayLiteral(children) => children.iter_mut().for_each(visit),
         Self::ArrayIndex { array: lhs, index: rhs } | Self::BinaryOperator { lhs, rhs, .. } => {
            visit(lhs);
            visit(rhs);
         }
         Self::IfX(cond, then_expr, else_expr) => {
            visit(cond);
            visit(then_expr);
            visit(else_expr);
         }
         Self::UnaryOperator(_, child) | Self::FieldAccess(_, child) | Self::Cast { expr: child, .. } => visit(child),
         Self::StructLiteral(_, fields) => fields.values_mut().flatten().for_each(visit),
         Self::UnresolvedStructLiteral(_, fields, _) => fields
            .iter_mut()
            .filter_map(|(_, child)| child.as_mut())
            .for_each(visit),
         Self::BoolLiteral(_)
         | Self::StringLiteral(_)
         | Self::IntLiteral { .. }
         | Self::FloatLiteral(_)
         | Self::UnitLiteral
         | Self::Variable(_)
         | Self::EnumLiteral(_, _)
         | Self::BoundFcnLiteral(_, _)
         | Self::UnresolvedVariable(_)
         | Self::UnresolvedEnumLiteral(_, _)
         | Self::UnresolvedProcLiteral(_, _) => (),
      }
   }
}
