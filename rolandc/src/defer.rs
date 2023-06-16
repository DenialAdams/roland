use crate::parse::{
   statement_always_returns, AstPool, BlockNode, Expression, ExpressionId, ExpressionPool, ProcImplSource, Program,
   Statement, StatementId,
};

enum CfKind {
   Loop,
   Return,
}

struct InsertionPoint {
   insert_at: usize,
   num_stmts_at_point: usize,
   kind: CfKind,
}

struct DeferContext {
   deferred_stmts: Vec<StatementId>,
   insertion_points: Vec<InsertionPoint>,
   num_stmts_at_loop_begin: usize,
}

pub fn process_defer_statements(program: &mut Program) {
   let mut ctx = DeferContext {
      deferred_stmts: Vec::new(),
      insertion_points: Vec::new(),
      num_stmts_at_loop_begin: 0,
   };

   for procedure in program.procedures.values_mut() {
      if let ProcImplSource::Body(block) = &mut procedure.proc_impl {
         defer_block(block, &mut ctx, &mut program.ast);
      }
   }
}

fn insert_deferred_stmt(point: usize, deferred_stmts: &[StatementId], block: &mut BlockNode, ast: &mut AstPool) {
   for (i, stmt) in deferred_stmts.iter().rev().copied().enumerate() {
      let new_stmt = deep_clone_stmt(stmt, ast);
      block.statements.insert(point + i, new_stmt);
   }
}

fn defer_block(block: &mut BlockNode, defer_ctx: &mut DeferContext, ast: &mut AstPool) {
   let deferred_stmts_before = defer_ctx.deferred_stmts.len();
   let insertion_points_before = defer_ctx.insertion_points.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      defer_statement(statement, defer_ctx, ast, current_stmt);
   }

   for point_details in defer_ctx.insertion_points.drain(insertion_points_before..).rev() {
      let deferred_stmts = match point_details.kind {
         CfKind::Loop => &defer_ctx.deferred_stmts[defer_ctx.num_stmts_at_loop_begin..point_details.num_stmts_at_point],
         CfKind::Return => &defer_ctx.deferred_stmts[..point_details.num_stmts_at_point],
      };
      insert_deferred_stmt(point_details.insert_at, deferred_stmts, block, ast);
   }

   if !block
      .statements
      .last()
      .copied()
      .map_or(false, |x| statement_always_returns(x, ast))
   {
      let deferred_exprs = &defer_ctx.deferred_stmts[deferred_stmts_before..];
      insert_deferred_stmt(block.statements.len(), deferred_exprs, block, ast);
   }

   defer_ctx.deferred_stmts.truncate(deferred_stmts_before);

   block.statements.retain(|x| {
      if let Statement::Defer(stmt_id) = ast.statements[*x].statement {
         // todo: this is a shallow delete of the stmt
         // we should probably delete deeply or not delete it at all
         ast.statements.remove(stmt_id);
         ast.statements.remove(*x);
         false
      } else {
         true
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
            num_stmts_at_point: defer_ctx.deferred_stmts.len(),
            kind: CfKind::Return,
         });
      }
      Statement::Break | Statement::Continue => {
         defer_ctx.insertion_points.push(InsertionPoint {
            insert_at: current_statement,
            num_stmts_at_point: defer_ctx.deferred_stmts.len(),
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
      Statement::Loop(block) => {
         let old = defer_ctx.num_stmts_at_loop_begin;
         defer_ctx.num_stmts_at_loop_begin = defer_ctx.deferred_stmts.len();
         defer_block(block, defer_ctx, ast);
         defer_ctx.num_stmts_at_loop_begin = old;
      }
      Statement::Defer(the_stmt) => {
         defer_statement(*the_stmt, defer_ctx, ast, current_statement);
         defer_ctx.deferred_stmts.push(*the_stmt);
      }
      Statement::Assignment(_, _) => (),
      Statement::Expression(_) => (),
      Statement::VariableDeclaration(_, _, _, _) => (),
      Statement::For { .. } => unreachable!(),
   }
   ast.statements[statement].statement = the_statement;
}

fn deep_clone_block(block: &mut BlockNode, ast: &mut AstPool) {
   for stmt in block.statements.iter_mut() {
      *stmt = deep_clone_stmt(*stmt, ast);
   }
}

#[must_use]
fn deep_clone_stmt(stmt: StatementId, ast: &mut AstPool) -> StatementId {
   let mut cloned = ast.statements[stmt].clone();
   match &mut cloned.statement {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(*lhs, &mut ast.expressions);
         *rhs = deep_clone_expr(*rhs, &mut ast.expressions);
      }
      Statement::Block(bn) => {
         deep_clone_block(bn, ast);
      }
      Statement::Loop(bn) => {
         deep_clone_block(bn, ast);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::Defer(stmt) => {
         *stmt = deep_clone_stmt(*stmt, ast);
      }
      Statement::Expression(expr) => {
         *expr = deep_clone_expr(*expr, &mut ast.expressions);
      }
      Statement::IfElse(cond, then, else_s) => {
         *cond = deep_clone_expr(*cond, &mut ast.expressions);
         deep_clone_block(then, ast);
         *else_s = deep_clone_stmt(*else_s, ast);
      }
      Statement::Return(expr) => {
         *expr = deep_clone_expr(*expr, &mut ast.expressions);
      }
      Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
      Statement::For { .. } => unreachable!(),
   }
   ast.statements.insert(cloned)
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
      Expression::UnresolvedVariable(_) | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
   }
   expressions.insert(cloned)
}
