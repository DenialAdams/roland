use std::collections::HashMap;

use indexmap::IndexMap;

use crate::{parse::{
   statement_always_or_never_returns, AstPool, BlockNode, DeclarationValue, Expression, ExpressionId, ExpressionPool, ProcImplSource, Program,
   Statement, StatementId, VariableId,
}, type_data::ExpressionType};

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
   for procedure in program.procedures.values_mut() {
      if let ProcImplSource::Body(block) = &mut procedure.proc_impl {
         vm.local_types = &mut procedure.locals;
         defer_block(block, &mut ctx, &mut program.ast, &mut vm);
      }
   }
}

fn insert_deferred_stmt(point: usize, deferred_stmts: &[StatementId], block: &mut BlockNode, ast: &mut AstPool, vm: &mut VarMigrator) {
   for (i, stmt) in deferred_stmts.iter().rev().copied().enumerate() {
      // Clearing the mapping here is correct, as long as we are going from the innermost defer out
      vm.mapping.clear();
      let new_stmt = deep_clone_stmt(stmt, ast, vm);
      block.statements.insert(point + i, new_stmt);
   }
}

fn defer_block(block: &mut BlockNode, defer_ctx: &mut DeferContext, ast: &mut AstPool, vm: &mut VarMigrator) {
   let deferred_stmts_before = defer_ctx.deferred_stmts.len();
   let insertion_points_before = defer_ctx.insertion_points.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      defer_statement(statement, defer_ctx, ast, current_stmt, vm);
   }

   for point_details in defer_ctx.insertion_points.drain(insertion_points_before..).rev() {
      let deferred_stmts = match point_details.kind {
         CfKind::Loop => &defer_ctx.deferred_stmts[defer_ctx.num_stmts_at_loop_begin..point_details.num_stmts_at_point],
         CfKind::Return => &defer_ctx.deferred_stmts[..point_details.num_stmts_at_point],
      };
      insert_deferred_stmt(point_details.insert_at, deferred_stmts, block, ast, vm);
   }

   if !block
      .statements
      .last()
      .copied()
      .map_or(false, |x| statement_always_or_never_returns(x, ast))
   {
      // There is an implicit final return
      let deferred_exprs = &defer_ctx.deferred_stmts[deferred_stmts_before..];
      insert_deferred_stmt(block.statements.len(), deferred_exprs, block, ast, vm);
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

fn defer_statement(statement: StatementId, defer_ctx: &mut DeferContext, ast: &mut AstPool, current_statement: usize, vm: &mut VarMigrator) {
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
      Statement::IfElse(_, if_block, else_statement) => {
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
      Statement::Assignment(_, _) => (),
      Statement::Expression(_) => (),
      Statement::VariableDeclaration(_, _, _, _) => (),
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
   }
   ast.statements[statement].statement = the_statement;
}

struct VarMigrator<'a> {
   next_var: &'a mut VariableId,
   mapping: HashMap<VariableId, VariableId>,
   local_types: &'a mut IndexMap<VariableId, ExpressionType>,
}

impl<'a> VarMigrator<'a> {
   fn new_var(&mut self, old_var: VariableId) -> VariableId {
      let new_var = std::mem::replace(self.next_var, self.next_var.next());
      self.mapping.insert(old_var, new_var);
      let existing_type = self.local_types.get(&old_var).unwrap().clone();
      self.local_types.insert(new_var, existing_type);
      new_var
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
      Statement::Block(bn) => {
         deep_clone_block(bn, ast, vm);
      }
      Statement::Loop(bn) => {
         deep_clone_block(bn, ast, vm);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::Defer(stmt) => {
         *stmt = deep_clone_stmt(*stmt, ast, vm);
      }
      Statement::Expression(expr) => {
         *expr = deep_clone_expr(*expr, &mut ast.expressions, vm);
      }
      Statement::IfElse(cond, then, else_s) => {
         *cond = deep_clone_expr(*cond, &mut ast.expressions, vm);
         deep_clone_block(then, ast, vm);
         *else_s = deep_clone_stmt(*else_s, ast, vm);
      }
      Statement::Return(expr) => {
         *expr = deep_clone_expr(*expr, &mut ast.expressions, vm);
      }
      Statement::VariableDeclaration(_, decl_val, _, var_id) => {
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
      Expression::ArrayIndex { array, index } => {
         *array = deep_clone_expr(*array, expressions, vm);
         *index = deep_clone_expr(*index, expressions, vm);
      }
      Expression::Variable(x) => {
         *x = vm.replacement_var(*x);
      },
      Expression::BinaryOperator { lhs, rhs, .. } => {
         *lhs = deep_clone_expr(*lhs, expressions, vm);
         *rhs = deep_clone_expr(*rhs, expressions, vm);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, expressions, vm);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.values_mut().flatten() {
            *field_expr = deep_clone_expr(*field_expr, expressions, vm);
         }
      }
      Expression::FieldAccess(_, base) => {
         *base = deep_clone_expr(*base, expressions, vm);
      }
      Expression::Cast { expr, .. } => {
         *expr = deep_clone_expr(*expr, expressions, vm);
      }
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(_, _) => (),
      Expression::UnresolvedVariable(_) | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
   expressions.insert(cloned)
}
