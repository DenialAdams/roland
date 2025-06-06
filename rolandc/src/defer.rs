use std::collections::HashMap;

use indexmap::IndexMap;

use crate::constant_folding::expression_could_have_side_effects;
use crate::parse::{
   AstPool, BlockNode, DeclarationValue, Expression, ExpressionId, ExpressionNode, ExpressionPool, Program, Statement,
   StatementId, StatementNode, VariableId, statement_always_or_never_returns,
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

   let mut vm = VarMigrator {
      mapping: HashMap::new(),
      next_var: &mut program.next_variable,
      local_types: &mut IndexMap::new(),
   };
   for body in program.procedure_bodies.values_mut() {
      vm.local_types = &mut body.locals;
      defer_block(&mut body.block, &mut ctx, &mut program.ast, &mut vm);
   }
}

fn insert_deferred_stmt(
   point: usize,
   deferred_stmts: &[StatementId],
   block: &mut BlockNode,
   ast: &mut AstPool,
   vm: &mut VarMigrator,
) {
   let mut inserted_stmts: usize = 0;

   if deferred_stmts.is_empty() {
      // This early return prevents us from hoisting out of the return statement
      // when it's not necessary
      return;
   }

   if let Some(Statement::Return(e)) = block.statements.get(point).map(|i| &ast.statements[*i].statement) {
      let e = *e;
      if expression_could_have_side_effects(e, &ast.expressions) {
         // We want the deferred statement to semantically execute AFTER the returned expression
         // So, we hoist before inserting the deferred stmt.
         let temp = {
            let var_id = *vm.next_var;
            *vm.next_var = vm.next_var.next();
            vm.local_types
               .insert(var_id, ast.expressions[e].exp_type.clone().unwrap());
            var_id
         };

         let location = ast.expressions[e].location;

         let temp_expression_node = ExpressionNode {
            expression: Expression::Variable(temp),
            exp_type: ast.expressions[e].exp_type.clone(),
            location,
         };

         let temp_assign = {
            let lhs = ast.expressions.insert(temp_expression_node);
            let rhs = ast.expressions.insert(ast.expressions[e].clone());
            ast.statements.insert(StatementNode {
               statement: Statement::Assignment(lhs, rhs),
               location,
            })
         };
         block.statements.insert(point, temp_assign);
         ast.expressions[e].expression = Expression::Variable(temp);

         inserted_stmts += 1;
      }
   }

   for stmt in deferred_stmts.iter().rev().copied() {
      // Clearing the mapping here is correct, as long as we are going from the innermost defer out
      vm.mapping.clear();
      let new_stmt = deep_clone_stmt(stmt, ast, vm);
      block.statements.insert(point + inserted_stmts, new_stmt);
      inserted_stmts += 1;
   }
}

fn defer_block(block: &mut BlockNode, defer_ctx: &mut DeferContext, ast: &mut AstPool, vm: &mut VarMigrator) {
   let deferred_stmts_before = defer_ctx.deferred_stmts.len();
   let insertion_points_before = defer_ctx.insertion_points.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      defer_statement(statement, defer_ctx, ast, current_stmt, vm);
   }

   if !block
      .statements
      .last()
      .copied()
      .is_some_and(|x| statement_always_or_never_returns(x, ast))
   {
      // Falling out of the scope
      let deferred_stmts = &defer_ctx.deferred_stmts[deferred_stmts_before..];
      insert_deferred_stmt(block.statements.len(), deferred_stmts, block, ast, vm);
   }

   for point_details in defer_ctx.insertion_points.drain(insertion_points_before..).rev() {
      let deferred_stmts = match point_details.kind {
         CfKind::Loop => &defer_ctx.deferred_stmts[defer_ctx.num_stmts_at_loop_begin..point_details.num_stmts_at_point],
         CfKind::Return => &defer_ctx.deferred_stmts[..point_details.num_stmts_at_point],
      };
      insert_deferred_stmt(point_details.insert_at, deferred_stmts, block, ast, vm);
   }

   defer_ctx.deferred_stmts.truncate(deferred_stmts_before);

   block
      .statements
      .retain(|x| !matches!(ast.statements[*x].statement, Statement::Defer(_)));
}

fn defer_statement(
   statement: StatementId,
   defer_ctx: &mut DeferContext,
   ast: &mut AstPool,
   current_statement: usize,
   vm: &mut VarMigrator,
) {
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
         defer_block(block, defer_ctx, ast, vm);
      }
      Statement::IfElse {
         cond: _,
         then: if_block,
         otherwise: else_statement,
         constant: _,
      } => {
         defer_block(if_block, defer_ctx, ast, vm);
         defer_statement(*else_statement, defer_ctx, ast, current_statement, vm);
      }
      Statement::Loop(block) => {
         let old = defer_ctx.num_stmts_at_loop_begin;
         defer_ctx.num_stmts_at_loop_begin = defer_ctx.deferred_stmts.len();
         defer_block(block, defer_ctx, ast, vm);
         defer_ctx.num_stmts_at_loop_begin = old;
      }
      Statement::Defer(the_stmt) => {
         defer_statement(*the_stmt, defer_ctx, ast, current_statement, vm);
         defer_ctx.deferred_stmts.push(*the_stmt);
      }
      Statement::Assignment(_, _) | Statement::Expression(_) | Statement::VariableDeclaration { .. } => (),
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
   }
   ast.statements[statement].statement = the_statement;
}

struct VarMigrator<'a> {
   next_var: &'a mut VariableId,
   mapping: HashMap<VariableId, VariableId>,
   local_types: &'a mut IndexMap<VariableId, ExpressionType>,
}

impl VarMigrator<'_> {
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

   fn replacement_var(&self, the_var: VariableId) -> VariableId {
      self.mapping.get(&the_var).copied().unwrap_or(the_var)
   }
}

fn deep_clone_block(block: &mut BlockNode, ast: &mut AstPool, vm: &mut VarMigrator) {
   for stmt in block.statements.iter_mut() {
      *stmt = deep_clone_stmt(*stmt, ast, vm);
   }
}

#[must_use]
fn deep_clone_stmt(stmt: StatementId, ast: &mut AstPool, vm: &mut VarMigrator) -> StatementId {
   let mut cloned = ast.statements[stmt].clone();
   match &mut cloned.statement {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(*lhs, &mut ast.expressions, vm);
         *rhs = deep_clone_expr(*rhs, &mut ast.expressions, vm);
      }
      Statement::Block(bn) | Statement::Loop(bn) => {
         deep_clone_block(bn, ast, vm);
      }
      Statement::Continue | Statement::Break => (),
      Statement::Defer(stmt) => {
         *stmt = deep_clone_stmt(*stmt, ast, vm);
      }
      Statement::Expression(expr) | Statement::Return(expr) => {
         *expr = deep_clone_expr(*expr, &mut ast.expressions, vm);
      }
      Statement::IfElse {
         cond,
         then,
         otherwise: else_s,
         constant: _,
      } => {
         *cond = deep_clone_expr(*cond, &mut ast.expressions, vm);
         deep_clone_block(then, ast, vm);
         *else_s = deep_clone_stmt(*else_s, ast, vm);
      }
      Statement::VariableDeclaration {
         var_name: _,
         value: decl_val,
         declared_type: _,
         var_id,
         storage: _,
      } => {
         match decl_val {
            DeclarationValue::Expr(expr_id) => *expr_id = deep_clone_expr(*expr_id, &mut ast.expressions, vm),
            DeclarationValue::Uninit | DeclarationValue::None => (),
         }
         *var_id = vm.new_var(*var_id);
      }
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
   }
   ast.statements.insert(cloned)
}

#[must_use]
fn deep_clone_expr(expr: ExpressionId, expressions: &mut ExpressionPool, vm: &mut VarMigrator) -> ExpressionId {
   let mut cloned = expressions[expr].clone();
   match &mut cloned.expression {
      Expression::IfX(a, b, c) => {
         *a = deep_clone_expr(*a, expressions, vm);
         *b = deep_clone_expr(*b, expressions, vm);
         *c = deep_clone_expr(*c, expressions, vm);
      }
      Expression::ProcedureCall { proc_expr, args } => {
         *proc_expr = deep_clone_expr(*proc_expr, expressions, vm);
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(arg.expr, expressions, vm);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(*expr, expressions, vm);
         }
      }
      Expression::Variable(x) => {
         *x = vm.replacement_var(*x);
      }
      Expression::BinaryOperator { lhs: a, rhs: b, .. } | Expression::ArrayIndex { array: a, index: b } => {
         *a = deep_clone_expr(*a, expressions, vm);
         *b = deep_clone_expr(*b, expressions, vm);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, expressions, vm);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.values_mut().flatten() {
            *field_expr = deep_clone_expr(*field_expr, expressions, vm);
         }
      }
      Expression::FieldAccess(_, expr) | Expression::Cast { expr, .. } => {
         *expr = deep_clone_expr(*expr, expressions, vm);
      }
      Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral
      | Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _) => (),
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
   expressions.insert(cloned)
}
