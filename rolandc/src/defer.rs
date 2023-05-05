use crate::parse::{
   statement_always_returns, AstPool, BlockNode, Expression, ExpressionId, ExpressionPool, Program, Statement,
   StatementId, StatementNode,
};

struct DeferContext {
   deferred_exprs: Vec<ExpressionId>,
}

pub fn process_defer_statements(program: &mut Program) {
   let mut ctx = DeferContext {
      deferred_exprs: Vec::new(),
   };

   for procedure in program.procedures.values_mut() {
      defer_block(&mut procedure.block, &mut ctx, &mut program.ast);
   }
}

fn defer_block(block: &mut BlockNode, defer_ctx: &mut DeferContext, ast: &mut AstPool) {
   let before_len = defer_ctx.deferred_exprs.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      defer_statement(statement, defer_ctx, ast, current_stmt);
   }

   if !block
      .statements
      .last()
      .copied()
      .map_or(false, |x| statement_always_returns(x, ast))
   {
      let deferred_exprs = &defer_ctx.deferred_exprs[before_len..];
      for expr in deferred_exprs.iter().rev().copied() {
         let location = ast.expressions[expr].location;
         let new_stmt = ast.statements.insert(StatementNode {
            statement: Statement::Expression(deep_clone_expr(expr, &mut ast.expressions)),
            location,
         });
         block.statements.push(new_stmt);
      }
   }

   block.statements.drain_filter(|x| {
      if let Statement::Defer(expr_id) = ast.statements[*x].statement {
         // todo: this is a shallow delete of the expression
         // we should probably delete deeply or not delete it at all
         ast.expressions.remove(expr_id);
         ast.statements.remove(*x);
         true
      } else {
         false
      }
   });
}

fn defer_statement(statement: StatementId, defer_ctx: &mut DeferContext, ast: &mut AstPool, current_statement: usize) {
   // TODO: dummy stmt?
   let mut the_statement = std::mem::replace(&mut ast.statements[statement].statement, Statement::Break);
   match &mut the_statement {
      Statement::Break | Statement::Continue | Statement::Return(_) => {
         // Need to inset defer handling
      }
      Statement::Block(block) => {
         defer_block(block, defer_ctx, ast);
      }
      Statement::IfElse(_, if_block, else_statement) => {
         defer_block(if_block, defer_ctx, ast);
         defer_statement(*else_statement, defer_ctx, ast, current_statement);
      }
      Statement::For(_, _, _, block, _, _) => {
         defer_block(block, defer_ctx, ast);
      }
      Statement::Loop(block) => {
         defer_block(block, defer_ctx, ast);
      }
      Statement::Defer(the_expr) => {
         defer_ctx.deferred_exprs.push(*the_expr);
      }
      Statement::Assignment(_, _) => (),
      Statement::Expression(_) => (),
      Statement::VariableDeclaration(_, _, _, _) => (),
   }
   ast.statements[statement].statement = the_statement;
}

#[must_use]
fn deep_clone_expr(expr: ExpressionId, expressions: &mut ExpressionPool) -> ExpressionId {
   let mut cloned = expressions[expr].clone();
   match &mut cloned.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         *proc_expr = deep_clone_expr(*proc_expr, expressions);
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(arg.expr, expressions);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(*expr, expressions);
         }
      }
      Expression::ArrayIndex { array, index } => {
         *array = deep_clone_expr(*array, expressions);
         *index = deep_clone_expr(*index, expressions);
      }
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::Variable(_) => (),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         *lhs = deep_clone_expr(*lhs, expressions);
         *rhs = deep_clone_expr(*rhs, expressions);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, expressions);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.iter_mut() {
            field_expr.1 = deep_clone_expr(field_expr.1, expressions);
         }
      }
      Expression::FieldAccess(_, base) => {
         *base = deep_clone_expr(*base, expressions);
      }
      Expression::Cast { expr, .. } => {
         *expr = deep_clone_expr(*expr, expressions);
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(_, _) => (),
   }
   expressions.insert(cloned)
}
