use std::collections::HashMap;

use indexmap::IndexMap;

use crate::cloner::{Cloner, deep_clone_expr};
use crate::constant_folding::is_const;
use crate::parse::{
   AstPool, BlockNode, DeclarationValue, Expression, ExpressionNode, ExpressionPool, Program, Statement, StatementId,
   StatementNode, VariableId, statement_always_or_never_returns,
};
use crate::type_data::ExpressionType;

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

   let mut cloner = DeferCloner {
      mapping: HashMap::new(),
      next_var: &mut program.next_variable,
      local_types: &mut IndexMap::new(),
      ast: &mut AstPool::new(),
   };
   for body in program.procedure_bodies.values_mut() {
      cloner.local_types = &mut body.locals;
      cloner.ast = &mut body.ast;
      defer_block(&mut body.block, &mut ctx, &mut cloner);
   }
}

fn insert_deferred_stmt(point: usize, deferred_stmts: &[StatementId], block: &mut BlockNode, cloner: &mut DeferCloner) {
   let mut inserted_stmts: usize = 0;

   if deferred_stmts.is_empty() {
      // This early return prevents us from hoisting out of the return statement
      // when it's not necessary
      return;
   }

   if let Some(Statement::Return(e)) = block
      .statements
      .get(point)
      .map(|i| &cloner.ast.statements[*i].statement)
   {
      let e = *e;
      if !is_const(&cloner.ast.expressions[e].expression, &cloner.ast.expressions) {
         // We want the deferred statement to semantically execute AFTER the returned expression
         // Even a read of a variable must happen before a defer can change its value.
         // So, we hoist before inserting the deferred stmt.
         let temp = {
            let var_id = *cloner.next_var;
            *cloner.next_var = cloner.next_var.next();
            cloner
               .local_types
               .insert(var_id, cloner.ast.expressions[e].exp_type.clone().unwrap());
            var_id
         };

         let location = cloner.ast.expressions[e].location;

         let temp_expression_node = ExpressionNode {
            expression: Expression::Variable(temp),
            exp_type: cloner.ast.expressions[e].exp_type.clone(),
            location,
         };

         let temp_assign = {
            let lhs = cloner.ast.expressions.insert(temp_expression_node);
            let rhs = cloner.ast.expressions.insert(cloner.ast.expressions[e].clone());
            cloner.ast.statements.insert(StatementNode {
               statement: Statement::Assignment(lhs, rhs),
               location,
            })
         };
         block.statements.insert(point, temp_assign);
         cloner.ast.expressions[e].expression = Expression::Variable(temp);

         inserted_stmts += 1;
      }
   }

   for stmt in deferred_stmts.iter().rev().copied() {
      // Clearing the mapping here is correct, as long as we are going from the innermost defer out
      cloner.mapping.clear();
      let new_stmt = deep_clone_stmt(stmt, cloner);
      block.statements.insert(point + inserted_stmts, new_stmt);
      inserted_stmts += 1;
   }
}

fn defer_block(block: &mut BlockNode, defer_ctx: &mut DeferContext, cloner: &mut DeferCloner) {
   let deferred_stmts_before = defer_ctx.deferred_stmts.len();
   let insertion_points_before = defer_ctx.insertion_points.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      defer_statement(statement, defer_ctx, current_stmt, cloner);
   }

   if !block
      .statements
      .last()
      .copied()
      .is_some_and(|x| statement_always_or_never_returns(x, cloner.ast))
   {
      // Falling out of the scope
      let deferred_stmts = &defer_ctx.deferred_stmts[deferred_stmts_before..];
      insert_deferred_stmt(block.statements.len(), deferred_stmts, block, cloner);
   }

   for point_details in defer_ctx.insertion_points.drain(insertion_points_before..).rev() {
      let deferred_stmts = match point_details.kind {
         CfKind::Loop => &defer_ctx.deferred_stmts[defer_ctx.num_stmts_at_loop_begin..point_details.num_stmts_at_point],
         CfKind::Return => &defer_ctx.deferred_stmts[..point_details.num_stmts_at_point],
      };
      insert_deferred_stmt(point_details.insert_at, deferred_stmts, block, cloner);
   }

   defer_ctx.deferred_stmts.truncate(deferred_stmts_before);

   block
      .statements
      .retain(|x| !matches!(cloner.ast.statements[*x].statement, Statement::Defer(_)));
}

fn defer_statement(
   statement: StatementId,
   defer_ctx: &mut DeferContext,
   current_statement: usize,
   cloner: &mut DeferCloner,
) {
   let mut the_statement = std::mem::replace(&mut cloner.ast.statements[statement].statement, Statement::Break);
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
         defer_block(block, defer_ctx, cloner);
      }
      Statement::IfElse {
         cond: _,
         then: if_block,
         otherwise: else_statement,
         constant: _,
      } => {
         defer_block(if_block, defer_ctx, cloner);
         defer_statement(*else_statement, defer_ctx, current_statement, cloner);
      }
      Statement::Loop(block) => {
         let old = defer_ctx.num_stmts_at_loop_begin;
         defer_ctx.num_stmts_at_loop_begin = defer_ctx.deferred_stmts.len();
         defer_block(block, defer_ctx, cloner);
         defer_ctx.num_stmts_at_loop_begin = old;
      }
      Statement::Defer(the_stmt) => {
         defer_statement(*the_stmt, defer_ctx, current_statement, cloner);
         defer_ctx.deferred_stmts.push(*the_stmt);
      }
      Statement::Assignment(_, _) | Statement::Expression(_) | Statement::VariableDeclaration { .. } => (),
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
   }
   cloner.ast.statements[statement].statement = the_statement;
}

struct DeferCloner<'a> {
   next_var: &'a mut VariableId,
   mapping: HashMap<VariableId, VariableId>,
   local_types: &'a mut IndexMap<VariableId, ExpressionType>,
   ast: &'a mut AstPool,
}

impl DeferCloner<'_> {
   fn new_var(&mut self, old_var: VariableId) -> VariableId {
      if let Some(existing_local_type) = self.local_types.get(&old_var) {
         let new_var = std::mem::replace(self.next_var, self.next_var.next());
         self.mapping.insert(old_var, new_var);
         self.local_types.insert(new_var, existing_local_type.clone());
         new_var
      } else {
         // For consts and statics, do nothing.
         // For consts, not cloning will not affect semantics.
         // For statics, we explicitly want there to only be one variable.
         // We are relying on the fact that const and static var declarations are lowered to nothing,
         // otherwise we would need to ensure that we skip the var decalartion when cloning for defer.
         old_var
      }
   }
}

impl Cloner for DeferCloner<'_> {
   fn replacement_var(&self, the_var: VariableId) -> VariableId {
      self.mapping.get(&the_var).copied().unwrap_or(the_var)
   }

   fn src_pool(&self) -> &ExpressionPool {
      &self.ast.expressions
   }

   fn dst_pool(&mut self) -> &mut ExpressionPool {
      &mut self.ast.expressions
   }
}

fn deep_clone_block(block: &mut BlockNode, cloner: &mut DeferCloner) {
   for stmt in block.statements.iter_mut() {
      *stmt = deep_clone_stmt(*stmt, cloner);
   }
}

#[must_use]
fn deep_clone_stmt(stmt: StatementId, cloner: &mut DeferCloner) -> StatementId {
   let mut cloned_stmt = cloner.ast.statements[stmt].clone();
   match &mut cloned_stmt.statement {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(*lhs, cloner);
         *rhs = deep_clone_expr(*rhs, cloner);
      }
      Statement::Block(bn) | Statement::Loop(bn) => {
         deep_clone_block(bn, cloner);
      }
      Statement::Continue | Statement::Break => (),
      Statement::Defer(stmt) => {
         *stmt = deep_clone_stmt(*stmt, cloner);
      }
      Statement::Expression(expr) | Statement::Return(expr) => {
         *expr = deep_clone_expr(*expr, cloner);
      }
      Statement::IfElse {
         cond,
         then,
         otherwise: else_s,
         constant: _,
      } => {
         *cond = deep_clone_expr(*cond, cloner);
         deep_clone_block(then, cloner);
         *else_s = deep_clone_stmt(*else_s, cloner);
      }
      Statement::VariableDeclaration {
         var_name: _,
         value: decl_val,
         declared_type: _,
         var_id,
         storage: _,
      } => {
         match decl_val {
            DeclarationValue::Expr(expr_id) => *expr_id = deep_clone_expr(*expr_id, cloner),
            DeclarationValue::Uninit | DeclarationValue::None => (),
         }
         *var_id = cloner.new_var(*var_id);
      }
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
   }
   cloner.ast.statements.insert(cloned_stmt)
}
