use indexmap::IndexMap;

use crate::parse::{
   AstPool, BinOp, BlockNode, Expression, ExpressionNode, Program, Statement, StatementId, StatementNode, UnOp,
   VariableId,
};
use crate::type_data::ExpressionType;

struct LowerForContext<'a> {
   for_stmts: Vec<usize>,
   next_variable: &'a mut VariableId,
   cur_procedure_locals: &'a mut IndexMap<VariableId, ExpressionType>,
}

pub fn lower_fors_and_whiles(program: &mut Program) {
   let mut ctx = LowerForContext {
      cur_procedure_locals: &mut IndexMap::new(),
      next_variable: &mut program.next_variable,
      for_stmts: Vec::new(),
   };

   for body in program.procedure_bodies.values_mut() {
      ctx.cur_procedure_locals = &mut body.locals;
      lower_block(&mut body.block, &mut ctx, &mut program.ast);
   }
}

fn lower_block(block: &mut BlockNode, ctx: &mut LowerForContext, ast: &mut AstPool) {
   let fors_before = ctx.for_stmts.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      lower_statement(statement, ctx, ast);
      if matches!(
         ast.statements[statement].statement,
         Statement::For { .. } | Statement::While(_, _)
      ) {
         ctx.for_stmts.push(current_stmt);
      }
   }

   for insertion_point in ctx.for_stmts.drain(fors_before..).rev() {
      let for_stmt = block.statements[insertion_point];

      let for_location = ast.statements[for_stmt].location;

      match ast.statements[for_stmt].statement {
         Statement::For {
            induction_var,
            range_start,
            range_end,
            ..
         } => {
            // Start assignment
            let start_assign = {
               let lhs_type = ast.expressions[range_start].exp_type.clone();
               let lhs = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(induction_var),
                  exp_type: lhs_type,
                  location: ast.expressions[range_start].location,
               });
               ast.statements.insert(StatementNode {
                  statement: Statement::Assignment(lhs, range_start),
                  location: ast.expressions[range_start].location,
               })
            };

            // End assignment
            let (end_assign, end_var) = {
               let var_id = *ctx.next_variable;
               *ctx.next_variable = ctx.next_variable.next();
               ctx.cur_procedure_locals
                  .insert(var_id, ast.expressions[range_end].exp_type.clone().unwrap());

               let lhs_type = ast.expressions[range_end].exp_type.clone();
               let lhs = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(var_id),
                  exp_type: lhs_type,
                  location: ast.expressions[range_end].location,
               });
               (
                  ast.statements.insert(StatementNode {
                     statement: Statement::Assignment(lhs, range_end),
                     location: ast.expressions[range_end].location,
                  }),
                  var_id,
               )
            };

            block
               .statements
               .splice(insertion_point..insertion_point, [start_assign, end_assign]);

            // If + Break
            let if_break = {
               let induction_var_type = ast.expressions[range_start].exp_type.clone();
               let induction_var_expr = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(induction_var),
                  exp_type: induction_var_type,
                  location: ast.expressions[range_start].location,
               });

               let end_type = ast.expressions[range_end].exp_type.clone();
               let end_var_expr = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(end_var),
                  exp_type: end_type,
                  location: ast.expressions[range_end].location,
               });

               let break_condition = ast.expressions.insert(ExpressionNode {
                  expression: Expression::BinaryOperator {
                     operator: BinOp::GreaterThanOrEqualTo,
                     lhs: induction_var_expr,
                     rhs: end_var_expr,
                  },
                  exp_type: Some(ExpressionType::Bool),
                  location: for_location,
               });

               let consequant = BlockNode {
                  statements: vec![ast.statements.insert(StatementNode {
                     statement: Statement::Break,
                     location: for_location,
                  })],
                  location: for_location,
               };

               let empty_else = ast.statements.insert(StatementNode {
                  statement: Statement::Block(BlockNode {
                     statements: vec![],
                     location: for_location,
                  }),
                  location: for_location,
               });

               ast.statements.insert(StatementNode {
                  statement: Statement::IfElse(break_condition, consequant, empty_else),
                  location: for_location,
               })
            };

            // Defer increment
            let deferred_increment = {
               let induction_var_type = ast.expressions[range_start].exp_type.clone();
               let induction_var_expr = ExpressionNode {
                  expression: Expression::Variable(induction_var),
                  exp_type: induction_var_type.clone(),
                  location: ast.expressions[range_start].location,
               };

               let one = ast.expressions.insert(ExpressionNode {
                  expression: Expression::IntLiteral {
                     val: 1,
                     synthetic: true,
                  },
                  exp_type: induction_var_type.clone(),
                  location: for_location,
               });

               let lhs = ast.expressions.insert(induction_var_expr.clone());
               let increment = ast.expressions.insert(ExpressionNode {
                  expression: Expression::BinaryOperator {
                     operator: BinOp::Add,
                     lhs,
                     rhs: one,
                  },
                  exp_type: induction_var_type,
                  location: for_location,
               });

               let assign = ast.statements.insert(StatementNode {
                  statement: Statement::Assignment(ast.expressions.insert(induction_var_expr.clone()), increment),
                  location: for_location,
               });

               ast.statements.insert(StatementNode {
                  statement: Statement::Defer(assign),
                  location: for_location,
               })
            };

            let Statement::For { ref mut body, .. } = ast.statements[for_stmt].statement else {
               unreachable!()
            };
            let mut body = std::mem::replace(
               body,
               BlockNode {
                  statements: vec![],
                  location: for_location,
               },
            );
            body.statements.splice(0..0, [if_break, deferred_increment]);

            ast.statements[for_stmt].statement = Statement::Loop(body);
         }
         Statement::While(while_condition, _) => {
            let if_break = {
               let consequant = BlockNode {
                  statements: vec![ast.statements.insert(StatementNode {
                     statement: Statement::Break,
                     location: for_location,
                  })],
                  location: for_location,
               };

               let empty_else = ast.statements.insert(StatementNode {
                  statement: Statement::Block(BlockNode {
                     statements: vec![],
                     location: for_location,
                  }),
                  location: for_location,
               });

               let negated_break_condition = ast.expressions.insert(ExpressionNode {
                  expression: Expression::UnaryOperator(UnOp::Complement, while_condition),
                  exp_type: Some(ExpressionType::Bool),
                  location: for_location,
               });

               ast.statements.insert(StatementNode {
                  statement: Statement::IfElse(negated_break_condition, consequant, empty_else),
                  location: for_location,
               })
            };

            let Statement::While(_, ref mut body) = ast.statements[for_stmt].statement else {
               unreachable!()
            };
            let mut body = std::mem::replace(
               body,
               BlockNode {
                  statements: vec![],
                  location: for_location,
               },
            );
            body.statements.insert(0, if_break);

            ast.statements[for_stmt].statement = Statement::Loop(body);
         }
         _ => unreachable!(),
      }
   }
}

fn lower_statement(statement: StatementId, ctx: &mut LowerForContext, ast: &mut AstPool) {
   let mut the_statement = std::mem::replace(&mut ast.statements[statement].statement, Statement::Break);
   match &mut the_statement {
      Statement::IfElse(_, if_block, else_statement) => {
         lower_block(if_block, ctx, ast);
         lower_statement(*else_statement, ctx, ast);
      }
      Statement::Block(block)
      | Statement::For { body: block, .. }
      | Statement::While(_, block)
      | Statement::Loop(block) => {
         lower_block(block, ctx, ast);
      }
      Statement::Defer(the_stmt) => {
         if matches!(ast.statements[*the_stmt].statement, Statement::For { .. }) {
            let location = ast.statements[*the_stmt].location;
            let new_block = ast.statements.insert(StatementNode {
               statement: Statement::Block(BlockNode {
                  statements: vec![*the_stmt],
                  location,
               }),
               location,
            });
            *the_stmt = new_block;
         }
         lower_statement(*the_stmt, ctx, ast);
      }
      Statement::Return(_)
      | Statement::Break
      | Statement::Continue
      | Statement::Assignment(_, _)
      | Statement::Expression(_)
      | Statement::VariableDeclaration(_, _, _, _) => (),
   }
   ast.statements[statement].statement = the_statement;
}
