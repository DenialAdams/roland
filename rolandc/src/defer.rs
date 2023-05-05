use crate::parse::{
   statement_always_returns, AstPool, BlockNode, Expression, ExpressionId, ExpressionPool, Program, Statement,
   StatementId, StatementNode,
};

enum CfKind {
   Loop,
   Return,
}

struct InsertionPoint {
   insert_at: usize,
   num_exprs_at_point: usize,
   kind: CfKind,
}

struct DeferContext {
   deferred_exprs: Vec<ExpressionId>,
   insertion_points: Vec<InsertionPoint>,
   num_exprs_at_loop_begin: usize,
}

pub fn process_defer_statements(program: &mut Program) {
   let mut ctx = DeferContext {
      deferred_exprs: Vec::new(),
      insertion_points: Vec::new(),
      num_exprs_at_loop_begin: 0,
   };

   for procedure in program.procedures.values_mut() {
      defer_block(&mut procedure.block, &mut ctx, &mut program.ast);
   }
}

fn insert_deferred_expr(point: usize, deferred_exprs: &[ExpressionId], block: &mut BlockNode, ast: &mut AstPool) {
   for (i, expr) in deferred_exprs.iter().rev().copied().enumerate() {
      let location = ast.expressions[expr].location;
      let new_stmt = ast.statements.insert(StatementNode {
         statement: Statement::Expression(deep_clone_expr(expr, &mut ast.expressions)),
         location,
      });
      block.statements.insert(point + i, new_stmt);
   }
}

fn defer_block(block: &mut BlockNode, defer_ctx: &mut DeferContext, ast: &mut AstPool) {
   let deferred_exprs_before = defer_ctx.deferred_exprs.len();
   let insertion_points_before = defer_ctx.insertion_points.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      defer_statement(statement, defer_ctx, ast, current_stmt);
   }

   for point_details in defer_ctx.insertion_points.drain(insertion_points_before..).rev() {
      let deferred_exprs = match point_details.kind {
         CfKind::Loop => &defer_ctx.deferred_exprs[defer_ctx.num_exprs_at_loop_begin..point_details.num_exprs_at_point],
         CfKind::Return => &defer_ctx.deferred_exprs[..point_details.num_exprs_at_point],
      };
      insert_deferred_expr(point_details.insert_at, deferred_exprs, block, ast);
   }

   if !block
      .statements
      .last()
      .copied()
      .map_or(false, |x| statement_always_returns(x, ast))
   {
      let deferred_exprs = &defer_ctx.deferred_exprs[deferred_exprs_before..];
      insert_deferred_expr(block.statements.len(), deferred_exprs, block, ast);
   }

   defer_ctx.deferred_exprs.truncate(deferred_exprs_before);

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
      Statement::Return(_) => {
         defer_ctx.insertion_points.push(InsertionPoint {
            insert_at: current_statement,
            num_exprs_at_point: defer_ctx.deferred_exprs.len(),
            kind: CfKind::Return,
         });
      }
      Statement::Break | Statement::Continue => {
         defer_ctx.insertion_points.push(InsertionPoint {
            insert_at: current_statement,
            num_exprs_at_point: defer_ctx.deferred_exprs.len(),
            kind: CfKind::Loop,
         });
      }
      Statement::Block(block) => {
         defer_block(block, defer_ctx, ast);
      }
      Statement::IfElse(_, if_block, else_statement) => {
         defer_block(if_block, defer_ctx, ast);
         defer_statement(*else_statement, defer_ctx, ast, current_statement);
      }
      Statement::For(_, _, _, block, _, _) | Statement::Loop(block) => {
         let old = defer_ctx.num_exprs_at_loop_begin;
         defer_ctx.num_exprs_at_loop_begin = defer_ctx.deferred_exprs.len();
         defer_block(block, defer_ctx, ast);
         defer_ctx.num_exprs_at_loop_begin = old;
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
