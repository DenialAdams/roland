use crate::parse::{BlockNode, Expression, ExpressionId, ProcedureNode, Statement, ExpressionNode};
use crate::Program;

trait TreeWalker {
   fn handle_statement_pre(&mut self, _: &mut Statement) {}
   fn handle_statement_post(&mut self, _: &mut Statement) {}

   fn handle_expression_pre(&mut self, _: ExpressionId) {}
   fn handle_expression_post(&mut self, _: ExpressionId) {}

   fn resolve_expr_id(&mut self, e: ExpressionId) -> *mut ExpressionNode;

   fn walk_expr(&mut self, e: ExpressionId) {
      match unsafe { &mut (*self.resolve_expr_id(e)).expression } {
         Expression::ArrayIndex { array, index } => {
            self.handle_expression_pre(*array);
            self.walk_expr(*array);
            self.handle_expression_post(*array);
            self.handle_expression_pre(*index);
            self.walk_expr(*index);
            self.handle_expression_post(*index);
         }
         Expression::ProcedureCall { args, .. } => {
            for arg in args.iter() {
               self.handle_expression_pre(arg.expr);
               self.walk_expr(arg.expr);
               self.handle_expression_post(arg.expr);
            }
         }
         Expression::BinaryOperator {
            operator: _operator,
            lhs,
            rhs,
         } => {
            self.handle_expression_pre(*lhs);
            self.walk_expr(*lhs);
            self.handle_expression_post(*lhs);
            self.handle_expression_pre(*rhs);
            self.walk_expr(*rhs);
            self.handle_expression_post(*rhs);
         }
         Expression::UnaryOperator(_op, expr) => {
            self.handle_expression_pre(*expr);
            self.walk_expr(*expr);
            self.handle_expression_post(*expr);         }
         Expression::StructLiteral(_, field_exprs) => {
            for (_, expr) in field_exprs.iter() {
               self.handle_expression_pre(*expr);
               self.walk_expr(*expr);
               self.handle_expression_post(*expr);            }
         }
         Expression::FieldAccess(_field_names, expr) => {
            self.handle_expression_pre(*expr);
            self.walk_expr(*expr);
            self.handle_expression_post(*expr);         }
         Expression::Cast { expr, .. } => {
            self.handle_expression_pre(*expr);
            self.walk_expr(*expr);
            self.handle_expression_post(*expr);         }
         Expression::ArrayLiteral(exprs) => {
            for expr in exprs.iter() {
               self.handle_expression_pre(*expr);
               self.walk_expr(*expr);
               self.handle_expression_post(*expr);            }
         }
         Expression::EnumLiteral(_, _) => (),
         Expression::BoolLiteral(_) => (),
         Expression::StringLiteral(_) => (),
         Expression::IntLiteral { .. } => (),
         Expression::FloatLiteral(_) => (),
         Expression::UnitLiteral => (),
         Expression::Variable(_) => (),
      }
   }

   fn walk_statement(&mut self, stmt: &mut Statement) {
      self.handle_statement_pre(stmt);
      match stmt {
         Statement::Assignment(lhs_expr, rhs_expr) => {
            self.handle_expression_pre(*lhs_expr);
            self.walk_expr(*lhs_expr);
            self.handle_expression_post(*lhs_expr);
            self.handle_expression_pre(*rhs_expr);
            self.walk_expr(*rhs_expr);
            self.handle_expression_post(*rhs_expr);
         }
         Statement::Block(block) => {
            self.walk_block(block);
         }
         Statement::Break | Statement::Continue => (),
         Statement::IfElse(if_expr, if_block, else_statement) => {
            self.handle_expression_pre(*if_expr);
            self.walk_expr(*if_expr);
            self.handle_expression_post(*if_expr);
            self.walk_block(if_block);
            self.handle_statement_pre(&mut else_statement.statement);
            self.walk_statement(&mut else_statement.statement);
            self.handle_statement_post(&mut else_statement.statement);
         }
         Statement::For(_var, start, end, block, _) => {
            self.handle_expression_pre(*start);
            self.walk_expr(*start);
            self.handle_expression_post(*start);
            self.handle_expression_pre(*end);
            self.walk_expr(*end);
            self.handle_expression_post(*end);
            self.walk_block(block);
         }
         Statement::Loop(block) => {
            self.walk_block(block);
         }
         Statement::Expression(expr) => {
            self.handle_expression_pre(*expr);
            self.walk_expr(*expr);
            self.handle_expression_post(*expr);
         }
         Statement::Return(expr) => {
            self.handle_expression_pre(*expr);
            self.walk_expr(*expr);
            self.handle_expression_post(*expr);
         }
         Statement::VariableDeclaration(_, expr, _) => {
            self.handle_expression_pre(*expr);
            self.walk_expr(*expr);
            self.handle_expression_post(*expr);
         }
      }
   }

   fn walk_block(&mut self, block: &mut BlockNode) {
      for stmt in block.statements.iter_mut() {
         self.handle_statement_pre(&mut stmt.statement);
         self.walk_statement(&mut stmt.statement);
         self.handle_statement_post(&mut stmt.statement);
      }
   }
}
