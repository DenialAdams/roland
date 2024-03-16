use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use crate::constant_folding::expression_could_have_side_effects;
use crate::parse::{
   AstPool, BlockNode, CastType, DeclarationValue, Expression, ExpressionId, ExpressionNode, ExpressionPool,
   ProcImplSource, Program, Statement, StatementId, StatementNode, UnOp, UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::{GlobalInfo, GlobalKind};
use crate::size_info::sizeof_type_mem;
use crate::type_data::ExpressionType;
use crate::Target;

pub fn is_reinterpretable_transmute(source_type: &ExpressionType, target_type: &ExpressionType) -> bool {
   source_type == target_type
      || matches!(
         (source_type, &target_type),
         (
            ExpressionType::Int(_)
               | ExpressionType::Float(_)
               | ExpressionType::Pointer(_)
               | ExpressionType::Bool
               | ExpressionType::Enum(_),
            ExpressionType::Int(_)
               | ExpressionType::Float(_)
               | ExpressionType::Pointer(_)
               | ExpressionType::Bool
               | ExpressionType::Enum(_)
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
   statements_that_need_hoisting: Vec<usize>,
   tac: bool,
   user_defined_types: &'a UserDefinedTypeInfo,
}

impl VvContext<'_> {
   fn mark_expr_for_hoisting(&mut self, expr_id: ExpressionId, current_stmt: usize, reason: HoistReason) {
      if reason == HoistReason::Must {
         self.statements_that_need_hoisting.push(current_stmt);
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
pub fn expression_hoisting(program: &mut Program, tac: bool) {
   let mut vv_context = VvContext {
      cur_procedure_locals: &mut IndexMap::new(),
      pending_hoists: IndexSet::new(),
      global_info: &program.global_info,
      next_variable: program.next_variable,
      statement_actions: Vec::new(),
      statements_that_need_hoisting: Vec::new(),
      tac,
      user_defined_types: &program.user_defined_types,
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

   let this_block_stmts_that_need_hoisting: HashSet<usize> = vv_context
      .statements_that_need_hoisting
      .drain(before_stmts_that_need_hoisting..)
      .collect();

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
   // so we can simply truncate instead of splitting off as we do for
   // the list of statement block indices
   vv_context.pending_hoists.truncate(before_pending_hoists);

   for if_stmt in new_ifs {
      let else_s = {
         let mut the_statement = std::mem::replace(&mut ast.statements[if_stmt].statement, Statement::Break);
         let Statement::IfElse(_, then_b, else_s) = &mut the_statement else {
            unreachable!()
         };
         let else_s = *else_s;
         vv_block(then_b, vv_context, ast);
         ast.statements[if_stmt].statement = the_statement;
         else_s
      };
      {
         let mut the_statement = std::mem::replace(&mut ast.statements[else_s].statement, Statement::Break);
         let Statement::Block(bn) = &mut the_statement else {
            unreachable!()
         };
         vv_block(bn, vv_context, ast);
         ast.statements[else_s].statement = the_statement;
      }
   }
}

fn vv_statement(statement: StatementId, vv_context: &mut VvContext, ast: &mut AstPool, current_statement: usize) {
   let mut the_statement = std::mem::replace(&mut ast.statements[statement].statement, Statement::Break);
   match &mut the_statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         vv_expr(
            *lhs_expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::AssignmentLhs,
            true,
         );
         vv_expr(
            *rhs_expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::AssignmentRhs,
            false,
         );
      }
      Statement::Block(block) => {
         vv_block(block, vv_context, ast);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse(if_expr, if_block, else_statement) => {
         vv_expr(
            *if_expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::IfCondition,
            false,
         );
         vv_block(if_block, vv_context, ast);
         vv_statement(*else_statement, vv_context, ast, current_statement);
      }
      Statement::Loop(block) => {
         vv_block(block, vv_context, ast);
      }
      Statement::Expression(expr) => {
         vv_expr(
            *expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::ExprStmt,
            false,
         );
      }
      Statement::Return(expr) => {
         vv_expr(
            *expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::Return,
            false,
         );
      }
      Statement::VariableDeclaration(str_node, opt_expr, _, var_id) => {
         if let DeclarationValue::Expr(expr) = opt_expr {
            vv_expr(
               *expr,
               vv_context,
               &ast.expressions,
               current_statement,
               ParentCtx::AssignmentRhs,
               false,
            );
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
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
   }
   ast.statements[statement].statement = the_statement;
}

#[derive(PartialEq)]
enum ParentCtx {
   ExprStmt,
   AssignmentLhs,
   AssignmentRhs,
   IfCondition,
   Return,
   Expr,
}

fn vv_expr(
   expr_index: ExpressionId,
   ctx: &mut VvContext,
   expressions: &ExpressionPool,
   current_stmt: usize,
   parent_ctx: ParentCtx,
   is_lhs_context: bool,
) {
   match &expressions[expr_index].expression {
      Expression::ArrayIndex { array, index } => {
         vv_expr(*array, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         vv_expr(*index, ctx, expressions, current_stmt, ParentCtx::Expr, false);
      }
      Expression::ProcedureCall { args, proc_expr } => {
         vv_expr(
            *proc_expr,
            ctx,
            expressions,
            current_stmt,
            ParentCtx::Expr,
            is_lhs_context,
         );

         for arg in args.iter() {
            vv_expr(
               arg.expr,
               ctx,
               expressions,
               current_stmt,
               ParentCtx::Expr,
               is_lhs_context,
            );
         }
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         vv_expr(*lhs, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         vv_expr(*rhs, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
      }
      Expression::UnaryOperator(UnOp::AddressOf, expr) => {
         if !expressions[*expr].expression.is_lvalue(expressions, ctx.global_info) {
            vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         } else {
            vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, true);
         }
      }
      Expression::UnaryOperator(UnOp::Dereference, expr) => {
         vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, false);
      }
      Expression::UnaryOperator(_, expr) => {
         vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for expr in field_exprs.values().flatten() {
            vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         }
      }
      Expression::FieldAccess(_field_names, expr) => {
         vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
      }
      Expression::Cast { expr, .. } => {
         vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         }
      }
      Expression::IfX(a, b, c) => {
         // IfX is hoisted specially, because it needs to become an if statement.
         // We still need to visit our children to see if we have to hoist this statement,
         // but we don't actually want to hoist B/C because that tree will be hoisted to the wrong spot
         // So what we do is we descend into B/C to allow for marking "this statement needs to be hoisted"
         // but then we pretend it didn't happen. Then, during hoisting we descend into the consequent/else
         // blocks that we create to do the marking and hoisting. Simple.
         vv_expr(*a, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         let before_len = ctx.statement_actions.len();
         let before_marked = ctx.pending_hoists.len();
         vv_expr(*b, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         vv_expr(*c, ctx, expressions, current_stmt, ParentCtx::Expr, is_lhs_context);
         ctx.statement_actions.truncate(before_len);
         ctx.pending_hoists.truncate(before_marked);
      }
      Expression::StringLiteral(_)
      | Expression::EnumLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::UnitLiteral
      | Expression::Variable(_) => (),
      Expression::UnresolvedVariable(_) | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }

   if ctx.tac {
      let is_ifx = matches!(expressions[expr_index].expression, Expression::IfX(_, _, _));
      let is_effective_top_level = (parent_ctx == ParentCtx::AssignmentRhs
         && sizeof_type_mem(
            expressions[expr_index].exp_type.as_ref().unwrap(),
            ctx.user_defined_types,
            Target::Qbe,
         ) == 0)
         || parent_ctx == ParentCtx::ExprStmt;
      let is_rhs_var = parent_ctx == ParentCtx::AssignmentRhs
         && matches!(expressions[expr_index].expression, Expression::Variable(_));
      let is_literal = matches!(
         expressions[expr_index].expression,
         Expression::BoundFcnLiteral(_, _)
            | Expression::IntLiteral { .. }
            | Expression::FloatLiteral { .. }
            | Expression::BoolLiteral { .. }
            | Expression::EnumLiteral { .. }
            | Expression::StringLiteral(_)
      );
      if is_ifx || (!is_lhs_context && !is_effective_top_level && !is_literal && !is_rhs_var) {
         ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
      }
   } else {
      match &expressions[expr_index].expression {
         Expression::ArrayIndex { array, .. } => {
            let array_expression = &expressions[*array];

            // If this is an rvalue, we need to store this array in memory to do the indexing
            // and hence hoist here.
            if !array_expression.expression.is_lvalue(expressions, ctx.global_info) {
               ctx.mark_expr_for_hoisting(*array, current_stmt, HoistReason::Must);
            }
         }
         Expression::ProcedureCall { args, proc_expr } => {
            let mut any_named_arg = false;
            for arg in args.iter() {
               any_named_arg |= arg.name.is_some();
            }

            if any_named_arg {
               for arg in args.iter() {
                  if expression_could_have_side_effects(arg.expr, expressions) {
                     ctx.statements_that_need_hoisting.push(current_stmt);
                     break;
                  }
               }
            }

            if matches!(
               expressions[*proc_expr].exp_type.as_ref().unwrap(),
               ExpressionType::ProcedurePointer { .. }
            ) && expression_could_have_side_effects(*proc_expr, expressions)
            {
               ctx.statements_that_need_hoisting.push(current_stmt);
            }

            let exp_type = expressions[expr_index].exp_type.as_ref().unwrap();

            // The point here is that we need to hoist calls where an aggregate is returned, because currently
            // a returned aggregate is an address _in the function we just called_, so not hoisting would mean
            // that we clobber the aggregate if we make another call. Because, currently, this hoisting runs before
            // monomorphization, we must also check size_is_unknown because any type parameter could end up
            // being an aggregate. This means unnecessary hoisting, unfortunately.
            if (exp_type.size_is_unknown() || exp_type.is_aggregate()) && parent_ctx == ParentCtx::Expr {
               ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
            }

            // assumption: procedure call always has side effects
            // If we eventually decide to come up with a list of pure procedure calls, this needs to be updated
            // @PureCalls
            if parent_ctx == ParentCtx::Expr {
               ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::IfOtherHoisting);
            }
         }
         Expression::UnaryOperator(UnOp::AddressOf, expr) => {
            if !expressions[*expr].expression.is_lvalue(expressions, ctx.global_info) {
               ctx.mark_expr_for_hoisting(*expr, current_stmt, HoistReason::Must);
            }
         }
         Expression::StructLiteral(_, field_exprs) => {
            for expr in field_exprs.values().flatten() {
               if expression_could_have_side_effects(*expr, expressions) {
                  ctx.statements_that_need_hoisting.push(current_stmt);
               }
            }
            if parent_ctx == ParentCtx::Expr {
               ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
            }
         }
         Expression::FieldAccess(_, expr) => {
            if !expressions[*expr].expression.is_lvalue(expressions, ctx.global_info) {
               ctx.mark_expr_for_hoisting(*expr, current_stmt, HoistReason::Must);
            }
         }
         Expression::Cast {
            cast_type: CastType::Transmute,
            expr,
            ..
         } => {
            let e = &expressions[*expr];

            if !e.expression.is_lvalue(expressions, ctx.global_info)
               && !is_reinterpretable_transmute(
                  e.exp_type.as_ref().unwrap(),
                  expressions[expr_index].exp_type.as_ref().unwrap(),
               )
            {
               ctx.mark_expr_for_hoisting(*expr, current_stmt, HoistReason::Must);
            }
         }
         Expression::ArrayLiteral(_) => {
            if parent_ctx == ParentCtx::Expr {
               ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
            }
         }
         Expression::IfX(_, _, _) => {
            ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::IfOtherHoisting);
         }
         Expression::StringLiteral(_) => {
            if parent_ctx == ParentCtx::Expr {
               ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
            }
         }
         Expression::Variable(x) => {
            // Pretty hacky.
            if ctx.global_info.get(x).map_or(false, |x| {
               x.kind == GlobalKind::Const && x.expr_type.e_type.is_aggregate()
            }) && parent_ctx == ParentCtx::Expr
            {
               ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
            }
         }
         Expression::UnresolvedVariable(_)
         | Expression::UnresolvedProcLiteral(_, _)
         | Expression::UnresolvedStructLiteral(_, _)
         | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
         _ => (),
      }
   }
}
