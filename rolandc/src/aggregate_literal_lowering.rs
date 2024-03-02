use indexmap::IndexMap;

use crate::interner::Interner;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionNode, ProcImplSource, Program, Statement, StatementId, StatementNode, UserDefinedTypeInfo, VariableId
};
use crate::type_data::{ExpressionType, U8_TYPE, USIZE_TYPE};

struct Context<'a> {
   local_types: &'a mut IndexMap<VariableId, ExpressionType>,
   next_var: &'a mut VariableId,
   aggregate_exprs_in_stmt: Vec<(ExpressionId, usize)>,
   user_defined_types: &'a UserDefinedTypeInfo,
   interner: &'a Interner,
}

pub fn lower_aggregate_literals(program: &mut Program, interner: &Interner) {
   let mut ctx = Context {
      local_types: &mut IndexMap::new(),
      next_var: &mut program.next_variable,
      aggregate_exprs_in_stmt: Vec::new(),
      user_defined_types: &program.user_defined_types,
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
         ctx
            .local_types
            .insert(var_id, ast.expressions[literal_expr].exp_type.clone().unwrap());
         var_id
      };

      let old_expr = std::mem::replace(&mut ast.expressions[literal_expr].expression, Expression::Variable(new_var));
      let location = ast.expressions[literal_expr].location;

      match old_expr {
         Expression::ArrayLiteral(children) => {
            for (i, child) in children.into_iter().enumerate().rev() {
               let arr_index_val = ast.expressions.insert(ExpressionNode {
                  expression: Expression::IntLiteral { val: i as u64, synthetic: true },
                  location,
                  exp_type: Some(USIZE_TYPE),
               });
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(new_var),
                  location,
                  exp_type: ast.expressions[literal_expr].exp_type.clone(),
               });
               let arr_index = ast.expressions.insert(ExpressionNode {
                  expression: Expression::ArrayIndex { array: base, index: arr_index_val },
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
         Expression::StructLiteral(s_id, fields) => {
            let si = ctx.user_defined_types.struct_info.get(s_id).unwrap();
            for field in si.field_types.iter().rev() {
               let rhs = match fields.get(field.0).copied() {
                  Some(Some(value_of_field)) => {
                     value_of_field
                  }
                  Some(None) => {
                     // Uninitialized
                     continue;
                  }
                  None => {
                     // Must be a default value
                     let default_value = si.default_values.get(field.0).copied().unwrap();

                     // We are sticking the default expression into the IR without cloning,
                     // which is bad. Even worse, if the default value is itself an aggregate
                     // literal, our goose is cooked. TODO we must lower default values prior
                     // to here.
                     default_value
                  }
               };
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(new_var),
                  location,
                  exp_type: ast.expressions[literal_expr].exp_type.clone(),
               });
               let field_access = ast.expressions.insert(ExpressionNode {
                  expression: Expression::FieldAccess(*field.0, base),
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
                  expression: Expression::IntLiteral { val: ctx.interner.lookup(s_val).len() as u64, synthetic: true },
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
         if expr_is_agg_literal(*e, ast) {
            ctx.aggregate_exprs_in_stmt.push((*e, current_statement));
         }
      }
      Statement::Block(block) => {
         lower_block(block, ctx, ast);
      }
      Statement::IfElse(cond, if_block, else_statement) => {
         if expr_is_agg_literal(*cond, ast) {
            ctx.aggregate_exprs_in_stmt.push((*cond, current_statement));
         }
         lower_block(if_block, ctx, ast);
         lower_statement(*else_statement, ctx, ast, current_statement);
      }
      Statement::Loop(block) => {
         lower_block(block, ctx, ast);
      }
      Statement::Assignment(lhs, rhs) => {
         if expr_is_agg_literal(*lhs, ast) {
            ctx.aggregate_exprs_in_stmt.push((*lhs, current_statement));
         }
         if expr_is_agg_literal(*rhs, ast) {
            ctx.aggregate_exprs_in_stmt.push((*rhs, current_statement));
         }
      },
      Statement::Break | Statement::Continue => (),
      Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
   }
   ast.statements[statement].statement = the_statement;
}

fn expr_is_agg_literal(expression: ExpressionId, ast: &AstPool) -> bool {
   matches!(ast.expressions[expression].expression, Expression::ArrayLiteral(_) | Expression::StructLiteral(_, _) | Expression::StringLiteral(_))
}
