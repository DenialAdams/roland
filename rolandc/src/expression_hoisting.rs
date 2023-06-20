use indexmap::{IndexMap, IndexSet};

use crate::constant_folding::expression_could_have_side_effects;
use crate::parse::{
   AstPool, BlockNode, CastType, Expression, ExpressionId, ExpressionNode, ExpressionPool, ProcImplSource, Program,
   Statement, StatementId, StatementNode, UnOp, VariableId,
};
use crate::semantic_analysis::GlobalInfo;
use crate::type_data::ExpressionType;

pub fn is_wasm_compatible_rval_transmute(source_type: &ExpressionType, target_type: &ExpressionType) -> bool {
   source_type == target_type
      || matches!(
         (source_type, &target_type),
         (
            ExpressionType::Int(_) | ExpressionType::Float(_),
            ExpressionType::Int(_) | ExpressionType::Float(_)
         )
      )
}

struct StmtAction {
   action: Action,
   stmt_anchor: usize,
}

#[derive(Copy, Clone, PartialEq)]
enum HoistReason {
   Must,
   IfOtherHoisting,
}

enum Action {
   Hoist { expr: ExpressionId },
   Delete,
}

struct VvContext<'a> {
   pending_hoists: IndexSet<ExpressionId>,
   cur_procedure_locals: &'a mut IndexMap<VariableId, ExpressionType>,
   global_info: &'a IndexMap<VariableId, GlobalInfo>,
   next_variable: VariableId,
   statement_actions: Vec<StmtAction>,
   statements_that_need_hoisting: IndexSet<usize>,
}

impl VvContext<'_> {
   fn mark_expr_for_hoisting(&mut self, expr_id: ExpressionId, current_stmt: usize, reason: HoistReason) {
      if reason == HoistReason::Must {
         self.statements_that_need_hoisting.insert(current_stmt);
      }
      if !self.pending_hoists.insert(expr_id) {
         return;
      }
      self.statement_actions.push(StmtAction {
         action: Action::Hoist { expr: expr_id },
         stmt_anchor: current_stmt,
      });
   }
}

// We hoist for a couple of different reasons:
// 1) Some operations are easier to sequence in the backend when side effects are pulled into separate statements (for loops, procedure calls, struct literals)
// 2) Some operations are easier to implement in the backend when rvalue's dont have to be considered (array indexing, field access, transmute)
// 3) Some operations don't make sense without operating on an lvalue (addressof)
// 4) The constant folder can't fold away an entire expression with side effects, but it can if the side effect is pulled out into a separate statement
//    - (this is of particular importance for field access - we need to lower all array length queries (which is pure type system info) before the backend)
pub fn expression_hoisting(program: &mut Program) {
   let mut vv_context = VvContext {
      cur_procedure_locals: &mut IndexMap::new(),
      pending_hoists: IndexSet::new(),
      global_info: &program.global_info,
      next_variable: program.next_variable,
      statement_actions: Vec::new(),
      statements_that_need_hoisting: IndexSet::new(),
   };

   for procedure in program.procedures.values_mut() {
      if let ProcImplSource::Body(block) = &mut procedure.proc_impl {
         vv_context.cur_procedure_locals = &mut procedure.locals;
         vv_block(block, &mut vv_context, &mut program.ast);
      }
   }

   program.next_variable = vv_context.next_variable;
}

fn vv_block(block: &mut BlockNode, vv_context: &mut VvContext, ast: &mut AstPool) {
   let before_vv_len = vv_context.statement_actions.len();
   let before_pending_hoists = vv_context.pending_hoists.len();
   let before_stmts_that_need_hoisting = vv_context.statements_that_need_hoisting.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      vv_statement(statement, vv_context, ast, current_stmt);
   }

   let this_block_stmts_that_need_hoisting = vv_context
      .statements_that_need_hoisting
      .split_off(before_stmts_that_need_hoisting);

   let mut new_ifs = vec![];
   for vv in vv_context.statement_actions.drain(before_vv_len..).rev() {
      match vv.action {
         Action::Hoist { expr } => {
            if !this_block_stmts_that_need_hoisting.contains(&vv.stmt_anchor) {
               continue;
            }

            let temp = {
               let var_id = vv_context.next_variable;
               vv_context.next_variable = vv_context.next_variable.next();
               vv_context
                  .cur_procedure_locals
                  .insert(var_id, ast.expressions[expr].exp_type.clone().unwrap());
               var_id
            };

            let location = ast.expressions[expr].location;

            let temp_expression_node = ExpressionNode {
               expression: Expression::Variable(temp),
               exp_type: ast.expressions[expr].exp_type.clone(),
               location,
            };

            if let Expression::IfX(a, b, c) = ast.expressions[expr].expression {
               let then_block = {
                  let temp_equals_b = {
                     let lhs = ast.expressions.insert(temp_expression_node.clone());
                     ast.statements.insert(StatementNode {
                        statement: Statement::Assignment(lhs, b),
                        location,
                     })
                  };
                  BlockNode {
                     statements: vec![temp_equals_b],
                     location,
                  }
               };
               let else_stmt = {
                  let temp_equals_c = {
                     let lhs = ast.expressions.insert(temp_expression_node.clone());
                     ast.statements.insert(StatementNode {
                        statement: Statement::Assignment(lhs, c),
                        location,
                     })
                  };
                  ast.statements.insert(StatementNode {
                     statement: Statement::Block(BlockNode {
                        statements: vec![temp_equals_c],
                        location,
                     }),
                     location,
                  })
               };
               let if_stmt = {
                  ast.statements.insert(StatementNode {
                     statement: Statement::IfElse(a, then_block, else_stmt),
                     location,
                  })
               };
               new_ifs.push(if_stmt);
               block.statements.insert(vv.stmt_anchor, if_stmt);
            } else {
               let temp_assign = {
                  let lhs = ast.expressions.insert(temp_expression_node);
                  let rhs = ast.expressions.insert(ast.expressions[expr].clone());
                  ast.statements.insert(StatementNode {
                     statement: Statement::Assignment(lhs, rhs),
                     location,
                  })
               };
               block.statements.insert(vv.stmt_anchor, temp_assign);
            }
            ast.expressions[expr].expression = Expression::Variable(temp);
         }
         Action::Delete => {
            let removed_stmt_id = block.statements.remove(vv.stmt_anchor);
            ast.statements.remove(removed_stmt_id);
         }
      }
   }

   // The same expression id shouldn't appear in the AST twice,
   // so we can simply truncate instead of splitting of as we do for
   // the list of statement block indices
   vv_context.pending_hoists.truncate(before_pending_hoists);

   for if_stmt in new_ifs {
      let else_s = {
         // TODO: dummy stmt?
         let mut the_statement = std::mem::replace(&mut ast.statements[if_stmt].statement, Statement::Break);
         let Statement::IfElse(_, then_b, else_s) = &mut the_statement else { unreachable!() };
         let else_s = *else_s;
         vv_block(then_b, vv_context, ast);
         ast.statements[if_stmt].statement = the_statement;
         else_s
      };
      {
         // TODO: dummy stmt?
         let mut the_statement = std::mem::replace(&mut ast.statements[else_s].statement, Statement::Break);
         let Statement::Block(bn) = &mut the_statement else { unreachable!() };
         vv_block(bn, vv_context, ast);
         ast.statements[else_s].statement = the_statement;
      }
   }
}

fn vv_statement(statement: StatementId, vv_context: &mut VvContext, ast: &mut AstPool, current_statement: usize) {
   // TODO: dummy stmt?
   let mut the_statement = std::mem::replace(&mut ast.statements[statement].statement, Statement::Break);
   match &mut the_statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         vv_expr(*lhs_expr, vv_context, &ast.expressions, current_statement, true);
         vv_expr(*rhs_expr, vv_context, &ast.expressions, current_statement, true);
      }
      Statement::Block(block) => {
         vv_block(block, vv_context, ast);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse(if_expr, if_block, else_statement) => {
         vv_expr(*if_expr, vv_context, &ast.expressions, current_statement, true);
         vv_block(if_block, vv_context, ast);
         vv_statement(*else_statement, vv_context, ast, current_statement);
      }
      Statement::Loop(block) => {
         vv_block(block, vv_context, ast);
      }
      Statement::Expression(expr) => {
         vv_expr(*expr, vv_context, &ast.expressions, current_statement, true);
      }
      Statement::Return(expr) => {
         vv_expr(*expr, vv_context, &ast.expressions, current_statement, true);
      }
      Statement::VariableDeclaration(str_node, opt_expr, _, var_id) => {
         if let Some(expr) = opt_expr {
            vv_expr(*expr, vv_context, &ast.expressions, current_statement, true);
            let lhs_type = vv_context.cur_procedure_locals.get(var_id).cloned();
            let lhs = ast.expressions.insert(ExpressionNode {
               expression: Expression::Variable(*var_id),
               exp_type: lhs_type,
               location: str_node.location,
            });
            the_statement = Statement::Assignment(lhs, *expr);
         } else {
            vv_context.statement_actions.push(StmtAction {
               action: Action::Delete,
               stmt_anchor: current_statement,
            });
         }
      }
      Statement::For { .. } => unreachable!(),
      Statement::Defer(_) => unreachable!(),
   }
   ast.statements[statement].statement = the_statement;
}

fn vv_expr(
   expr_index: ExpressionId,
   vv_context: &mut VvContext,
   expressions: &ExpressionPool,
   current_statement: usize,
   top: bool,
) {
   match &expressions[expr_index].expression {
      Expression::ArrayIndex { array, index } => {
         vv_expr(*array, vv_context, expressions, current_statement, false);
         vv_expr(*index, vv_context, expressions, current_statement, false);

         let array_expression = &expressions[*array];

         // If this is an rvalue, we need to store this array in memory to do the indexing
         // and hence hoist here.
         if !array_expression
            .expression
            .is_lvalue(expressions, vv_context.global_info)
         {
            vv_context.mark_expr_for_hoisting(*array, current_statement, HoistReason::Must);
         }
      }
      Expression::ProcedureCall { args, proc_expr } => {
         vv_expr(*proc_expr, vv_context, expressions, current_statement, false);

         let mut any_named_arg = false;
         for arg in args.iter() {
            vv_expr(arg.expr, vv_context, expressions, current_statement, false);

            any_named_arg |= arg.name.is_some();
         }

         if any_named_arg {
            for arg in args.iter() {
               if expression_could_have_side_effects(arg.expr, expressions) {
                  vv_context.statements_that_need_hoisting.insert(current_statement);
                  break;
               }
            }
         }

         if matches!(
            expressions[*proc_expr].exp_type.as_ref().unwrap(),
            ExpressionType::ProcedurePointer { .. }
         ) && expression_could_have_side_effects(*proc_expr, expressions)
         {
            vv_context.statements_that_need_hoisting.insert(current_statement);
         }
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         vv_expr(*lhs, vv_context, expressions, current_statement, false);
         vv_expr(*rhs, vv_context, expressions, current_statement, false);
      }
      Expression::UnaryOperator(op, expr) => {
         vv_expr(*expr, vv_context, expressions, current_statement, false);

         if *op == UnOp::AddressOf
            && !expressions[*expr]
               .expression
               .is_lvalue(expressions, vv_context.global_info)
         {
            vv_context.mark_expr_for_hoisting(*expr, current_statement, HoistReason::Must);
         }
      }
      Expression::StructLiteral(_, field_exprs) => {
         for expr in field_exprs.values().flatten() {
            vv_expr(*expr, vv_context, expressions, current_statement, false);
            if expression_could_have_side_effects(*expr, expressions) {
               vv_context.statements_that_need_hoisting.insert(current_statement);
            }
         }
      }
      Expression::FieldAccess(_field_names, expr) => {
         vv_expr(*expr, vv_context, expressions, current_statement, false);

         if !expressions[*expr]
            .expression
            .is_lvalue(expressions, vv_context.global_info)
         {
            vv_context.mark_expr_for_hoisting(*expr, current_statement, HoistReason::Must);
         }
      }
      Expression::Cast {
         cast_type: CastType::Transmute,
         expr,
         ..
      } => {
         vv_expr(*expr, vv_context, expressions, current_statement, false);

         let e = &expressions[*expr];

         if !e.expression.is_lvalue(expressions, vv_context.global_info)
            && !is_wasm_compatible_rval_transmute(
               e.exp_type.as_ref().unwrap(),
               expressions[expr_index].exp_type.as_ref().unwrap(),
            )
         {
            vv_context.mark_expr_for_hoisting(*expr, current_statement, HoistReason::Must);
         }
      }
      Expression::Cast { expr, .. } => {
         vv_expr(*expr, vv_context, expressions, current_statement, false);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            vv_expr(*expr, vv_context, expressions, current_statement, false);
         }
      }
      Expression::IfX(a, b, c) => {
         // IfX is hoisted specially, because it needs to become an if statement.
         // We still need to visit our children to see if we have to hoist this statement,
         // but we don't actually want to hoist B/C because that tree will be hoisted to the wrong spot
         // So what we do is we descend into B/C to allow for marking "this statement needs to be hoisted"
         // but then we pretend it didn't happen. Then, during hoisting we descend into the consequent/else
         // blocks that we create to do the marking and hoisting. Simple.
         vv_expr(*a, vv_context, expressions, current_statement, false);
         let before_len = vv_context.statement_actions.len();
         let before_marked = vv_context.pending_hoists.len();
         vv_expr(*b, vv_context, expressions, current_statement, false);
         vv_expr(*c, vv_context, expressions, current_statement, false);
         vv_context.statement_actions.truncate(before_len);
         vv_context.pending_hoists.truncate(before_marked);
         vv_context.mark_expr_for_hoisting(expr_index, current_statement, HoistReason::IfOtherHoisting);
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::BoundFcnLiteral(_, _) => (),
      Expression::UnitLiteral => (),
      Expression::Variable(_) => (),
      Expression::UnresolvedVariable(_) | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) => unreachable!(),
   }

   // assumption: procedure call is the only leaf node with side effects, and always has side effects
   // If we eventually decide to come up with a list of pure procedure calls, this needs to be updated
   // @PureCalls
   if matches!(expressions[expr_index].expression, Expression::ProcedureCall { .. }) && !top {
      vv_context.mark_expr_for_hoisting(expr_index, current_statement, HoistReason::IfOtherHoisting);
   }
}
