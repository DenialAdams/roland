use indexmap::IndexMap;

use crate::interner::Interner;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionNode, ProcImplSource, Program, Statement, StatementId,
   StatementNode, VariableId,
};
use crate::type_data::{ExpressionType, U8_TYPE, USIZE_TYPE};

struct Context<'a> {
   local_types: &'a mut IndexMap<VariableId, ExpressionType>,
   next_var: &'a mut VariableId,
   aggregate_exprs_in_stmt: Vec<(ExpressionId, usize)>,
   interner: &'a Interner,
}

pub fn lower_aggregate_literals(program: &mut Program, interner: &Interner) {
   let mut ctx = Context {
      local_types: &mut IndexMap::new(),
      next_var: &mut program.next_variable,
      aggregate_exprs_in_stmt: Vec::new(),
      interner,
   };

   for procedure in program.procedures.values_mut() {
      if let ProcImplSource::Body(block) = &mut procedure.proc_impl {
         ctx.local_types = &mut procedure.locals;
         lower_block(block, &mut ctx, &mut program.ast);
      }
   }
}

fn lower_block(block: &mut BlockNode, ctx: &mut Context, ast: &mut AstPool) {
   let len_before = ctx.aggregate_exprs_in_stmt.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      lower_statement(statement, ctx, ast, current_stmt);
   }
   for (literal_expr, stmt_index) in ctx.aggregate_exprs_in_stmt.drain(len_before..).rev() {
      let new_var = {
         let var_id = *ctx.next_var;
         *ctx.next_var = ctx.next_var.next();
         ctx.local_types
            .insert(var_id, ast.expressions[literal_expr].exp_type.clone().unwrap());
         var_id
      };

      let old_expr = std::mem::replace(
         &mut ast.expressions[literal_expr].expression,
         Expression::Variable(new_var),
      );
      let location = ast.expressions[literal_expr].location;

      match old_expr {
         Expression::ArrayLiteral(children) => {
            for (i, child) in children.iter().enumerate().rev() {
               let arr_index_val = ast.expressions.insert(ExpressionNode {
                  expression: Expression::IntLiteral {
                     val: i as u64,
                     synthetic: true,
                  },
                  location,
                  exp_type: Some(USIZE_TYPE),
               });
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(new_var),
                  location,
                  exp_type: ast.expressions[literal_expr].exp_type.clone(),
               });
               let arr_index = ast.expressions.insert(ExpressionNode {
                  expression: Expression::ArrayIndex {
                     array: base,
                     index: arr_index_val,
                  },
                  location,
                  exp_type: ast.expressions[*child].exp_type.clone(),
               });
               let assignment = ast.statements.insert(StatementNode {
                  location,
                  statement: Statement::Assignment(arr_index, *child),
               });
               block.statements.insert(stmt_index, assignment);
            }
         }
         Expression::StructLiteral(_, fields) => {
            for field in fields.into_iter().rev() {
               let Some(rhs) = field.1 else {
                  // Uninitialized
                  continue;
               };
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(new_var),
                  location,
                  exp_type: ast.expressions[literal_expr].exp_type.clone(),
               });
               let field_access = ast.expressions.insert(ExpressionNode {
                  expression: Expression::FieldAccess(field.0, base),
                  location,
                  exp_type: ast.expressions[rhs].exp_type.clone(),
               });
               let assignment = ast.statements.insert(StatementNode {
                  location,
                  statement: Statement::Assignment(field_access, rhs),
               });
               block.statements.insert(stmt_index, assignment);
            }
         }
         Expression::StringLiteral(s_val) => {
            // length
            {
               let rhs = ast.expressions.insert(ExpressionNode {
                  expression: Expression::IntLiteral {
                     val: ctx.interner.lookup(s_val).len() as u64,
                     synthetic: true,
                  },
                  location,
                  exp_type: Some(USIZE_TYPE),
               });
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(new_var),
                  location,
                  exp_type: ast.expressions[literal_expr].exp_type.clone(),
               });
               let field_access = ast.expressions.insert(ExpressionNode {
                  expression: Expression::FieldAccess(ctx.interner.reverse_lookup("length").unwrap(), base),
                  location,
                  exp_type: ast.expressions[rhs].exp_type.clone(),
               });
               let assignment = ast.statements.insert(StatementNode {
                  location,
                  statement: Statement::Assignment(field_access, rhs),
               });
               block.statements.insert(stmt_index, assignment);
            }

            // Pointer
            {
               let rhs = ast.expressions.insert(ExpressionNode {
                  expression: Expression::StringLiteral(s_val),
                  location,
                  exp_type: Some(ExpressionType::Pointer(Box::new(U8_TYPE))),
               });
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(new_var),
                  location,
                  exp_type: ast.expressions[literal_expr].exp_type.clone(),
               });
               let field_access = ast.expressions.insert(ExpressionNode {
                  expression: Expression::FieldAccess(ctx.interner.reverse_lookup("pointer").unwrap(), base),
                  location,
                  exp_type: ast.expressions[rhs].exp_type.clone(),
               });
               let assignment = ast.statements.insert(StatementNode {
                  location,
                  statement: Statement::Assignment(field_access, rhs),
               });
               block.statements.insert(stmt_index, assignment);
            }
         }
         _ => unreachable!(),
      }
   }
}

fn lower_statement(statement: StatementId, ctx: &mut Context, ast: &mut AstPool, current_statement: usize) {
   let mut the_statement = std::mem::replace(&mut ast.statements[statement].statement, Statement::Break);
   match &mut the_statement {
      Statement::Return(e) | Statement::Expression(e) => {
         lower_expr(*e, ctx, ast, current_statement);
      }
      Statement::Block(block) => {
         lower_block(block, ctx, ast);
      }
      Statement::IfElse(cond, if_block, else_statement) => {
         lower_expr(*cond, ctx, ast, current_statement);
         lower_block(if_block, ctx, ast);
         lower_statement(*else_statement, ctx, ast, current_statement);
      }
      Statement::Loop(block) => {
         lower_block(block, ctx, ast);
      }
      Statement::Assignment(lhs, rhs) => {
         lower_expr(*lhs, ctx, ast, current_statement);
         lower_expr(*rhs, ctx, ast, current_statement);
      }
      Statement::Break | Statement::Continue => (),
      Statement::VariableDeclaration(_, _, _, _)
      | Statement::For { .. }
      | Statement::While(_, _)
      | Statement::Defer(_) => unreachable!(),
   }
   ast.statements[statement].statement = the_statement;
}

fn lower_expr(expr: ExpressionId, ctx: &mut Context, ast: &AstPool, current_statement: usize) {
   match &ast.expressions[expr].expression {
      Expression::ArrayLiteral(elems) => {
         for elem in elems.iter().copied() {
            lower_expr(elem, ctx, ast, current_statement);
         }
         ctx.aggregate_exprs_in_stmt.push((expr, current_statement));
      }
      Expression::StructLiteral(_, fields) => {
         for field in fields.values().flatten().copied() {
            lower_expr(field, ctx, ast, current_statement);
         }
         ctx.aggregate_exprs_in_stmt.push((expr, current_statement));
      }
      Expression::StringLiteral(_) => {
         ctx.aggregate_exprs_in_stmt.push((expr, current_statement));
      }
      Expression::ProcedureCall { proc_expr, args } => {
         lower_expr(*proc_expr, ctx, ast, current_statement);
         for arg in args.iter().map(|x| x.expr) {
            lower_expr(arg, ctx, ast, current_statement);
         }
      }
      Expression::ArrayIndex { array: lhs, index: rhs } | Expression::BinaryOperator { lhs, rhs, .. } => {
         lower_expr(*lhs, ctx, ast, current_statement);
         lower_expr(*rhs, ctx, ast, current_statement);
      }
      Expression::Cast { expr: inner, .. }
      | Expression::UnaryOperator(_, inner)
      | Expression::FieldAccess(_, inner) => lower_expr(*inner, ctx, ast, current_statement),
      Expression::IfX(a, b, c) => {
         lower_expr(*a, ctx, ast, current_statement);
         lower_expr(*b, ctx, ast, current_statement);
         lower_expr(*c, ctx, ast, current_statement);
      }
      Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::EnumLiteral(_, _)
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral
      | Expression::Variable(_) => (),
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedStructLiteral(_, _)
      | Expression::UnresolvedEnumLiteral(_, _)
      | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
   }
}
