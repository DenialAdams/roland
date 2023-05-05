use crate::parse::{
   AstPool, BlockNode, CastType, Expression, ExpressionId, ExpressionNode, ExpressionPool, Program, Statement,
   StatementId, StatementNode,
};

struct DeferContext {
   defer_stmts: Vec<(usize, ExpressionId)>,
}

pub fn process_defer_statements(program: &mut Program) {
   let mut ctx = DeferContext {
      defer_stmts: Vec::new(),
   };

   for procedure in program.procedures.values_mut() {
      defer_block(&mut procedure.block, &mut ctx, &mut program.ast);
   }
}

fn defer_block(block: &mut BlockNode, defer_ctx: &mut DeferContext, ast: &mut AstPool) {
   let before_len = defer_ctx.defer_stmts.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      defer_statement(statement, defer_ctx, ast, current_stmt);
   }

   for (defer_stmt_index, _) in defer_ctx.defer_stmts.drain(before_len..).rev() {
      let removed_stmt_id = block.statements.remove(defer_stmt_index);
      ast.statements.remove(removed_stmt_id);
   }
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
         defer_ctx.defer_stmts.push((current_statement, *the_expr));
      }
      _ => (),
   }
   ast.statements[statement].statement = the_statement;
}
