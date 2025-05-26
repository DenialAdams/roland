use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use crate::Target;
use crate::constant_folding::{expression_could_have_side_effects, is_non_aggregate_const};
use crate::interner::Interner;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionNode, ExpressionPool, Program, Statement,
   StatementId, StatementNode, UnOp, UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::GlobalInfo;
use crate::size_info::sizeof_type_mem;
use crate::type_data::{ExpressionType, U8_TYPE, USIZE_TYPE};

#[derive(Copy, Clone, PartialEq)]
enum HoistReason {
   Must,
   IfOtherHoisting,
}

#[derive(PartialEq, Clone, Copy)]
pub enum HoistingMode {
   PreConstantFold,
   ThreeAddressCode,
   AggregateLiteralLowering,
}

struct ExprWithContainingStmtIndex {
   expr: ExpressionId,
   stmt_anchor: usize,
}

struct VvContext<'a> {
   pending_hoists: IndexSet<ExpressionId>,
   cur_procedure_locals: &'a mut IndexMap<VariableId, ExpressionType>,
   global_info: &'a IndexMap<VariableId, GlobalInfo>,
   next_variable: VariableId,
   exprs_to_hoist: Vec<ExprWithContainingStmtIndex>,
   statements_that_need_hoisting: Vec<usize>,
   mode: HoistingMode,
   user_defined_types: &'a UserDefinedTypeInfo,
   interner: &'a Interner,
}

impl VvContext<'_> {
   fn mark_expr_for_hoisting(&mut self, expr_id: ExpressionId, current_stmt: usize, reason: HoistReason) {
      if reason == HoistReason::Must {
         self.statements_that_need_hoisting.push(current_stmt);
      }
      if !self.pending_hoists.insert(expr_id) {
         return;
      }
      self.exprs_to_hoist.push(ExprWithContainingStmtIndex {
         expr: expr_id,
         stmt_anchor: current_stmt,
      });
   }
}

// We hoist for a couple of different reasons:
// 1) Some operations are easier to sequence in the backend when side effects are pulled into separate statements (procedure calls)
// 2) Some operations are easier to implement in the backend when rvalue's dont have to be considered (array indexing, field access, transmute)
// 3) Some operations don't make sense without operating on an lvalue (addressof)
// 4) The constant folder can't fold away an entire expression with side effects, but it can if the side effect is pulled out into a separate statement
//    - (this is of particular importance for field access - we need to lower all array length queries (which is pure type system info) before the backend)
pub fn expression_hoisting(program: &mut Program, interner: &Interner, mode: HoistingMode) {
   let mut vv_context = VvContext {
      cur_procedure_locals: &mut IndexMap::new(),
      pending_hoists: IndexSet::new(),
      global_info: &program.non_stack_var_info,
      next_variable: program.next_variable,
      exprs_to_hoist: Vec::new(),
      statements_that_need_hoisting: Vec::new(),
      mode,
      user_defined_types: &program.user_defined_types,
      interner,
   };

   for body in program.procedure_bodies.values_mut() {
      vv_context.cur_procedure_locals = &mut body.locals;
      vv_block(&mut body.block, &mut vv_context, &mut program.ast);
   }

   program.next_variable = vv_context.next_variable;
}

fn vv_block(block: &mut BlockNode, ctx: &mut VvContext, ast: &mut AstPool) {
   let before_vv_len = ctx.exprs_to_hoist.len();
   let before_pending_hoists = ctx.pending_hoists.len();
   let before_stmts_that_need_hoisting = ctx.statements_that_need_hoisting.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      vv_statement(statement, ctx, ast, current_stmt);
   }

   let this_block_stmts_that_need_hoisting: HashSet<usize> = ctx
      .statements_that_need_hoisting
      .drain(before_stmts_that_need_hoisting..)
      .collect();

   let mut new_ifs = vec![];
   for vv in ctx.exprs_to_hoist.drain(before_vv_len..).rev() {
      if !this_block_stmts_that_need_hoisting.contains(&vv.stmt_anchor) {
         continue;
      }

      let expr = vv.expr;

      let temp = {
         let var_id = ctx.next_variable;
         ctx.next_variable = ctx.next_variable.next();
         ctx.cur_procedure_locals
            .insert(var_id, ast.expressions[expr].exp_type.clone().unwrap());
         var_id
      };

      let location = ast.expressions[expr].location;

      let temp_expression_node = ExpressionNode {
         expression: Expression::Variable(temp),
         exp_type: ast.expressions[expr].exp_type.clone(),
         location,
      };

      // wat nocheckin
      let replacement_expr = if ctx.mode == HoistingMode::ThreeAddressCode {
         // the IR has been lowered such that variables are not implicitly converted to rvals
         let var_node = ast.expressions.insert(ExpressionNode {
            expression: Expression::Variable(temp),
            exp_type: Some(ExpressionType::Pointer(Box::new(ast.expressions[expr].exp_type.clone().unwrap()))),
            location,
         });
         Expression::UnaryOperator(UnOp::Dereference, var_node)
      } else {
         Expression::Variable(temp)
      };

      let old_expression = std::mem::replace(&mut ast.expressions[expr].expression, replacement_expr);
      match old_expression {
         Expression::IfX(a, b, c) => {
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
                  statement: Statement::IfElse {
                     cond: a,
                     then: then_block,
                     otherwise: else_stmt,
                     constant: false,
                  },
                  location,
               })
            };
            new_ifs.push(if_stmt);
            block.statements.insert(vv.stmt_anchor, if_stmt);
         }
         Expression::StringLiteral(s_val) if ctx.mode == HoistingMode::AggregateLiteralLowering => {
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
                  expression: Expression::Variable(temp),
                  location,
                  exp_type: ast.expressions[expr].exp_type.clone(),
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
               block.statements.insert(vv.stmt_anchor, assignment);
            }

            // Pointer
            {
               let rhs = ast.expressions.insert(ExpressionNode {
                  expression: Expression::StringLiteral(s_val),
                  location,
                  exp_type: Some(ExpressionType::Pointer(Box::new(U8_TYPE))),
               });
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(temp),
                  location,
                  exp_type: ast.expressions[expr].exp_type.clone(),
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
               block.statements.insert(vv.stmt_anchor, assignment);
            }
         }
         Expression::StructLiteral(_, fields) if ctx.mode == HoistingMode::AggregateLiteralLowering => {
            for field in fields.into_iter().rev() {
               let Some(rhs) = field.1 else {
                  // Uninitialized
                  continue;
               };
               let base = ast.expressions.insert(ExpressionNode {
                  expression: Expression::Variable(temp),
                  location,
                  exp_type: ast.expressions[expr].exp_type.clone(),
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
               block.statements.insert(vv.stmt_anchor, assignment);
            }
         }
         Expression::ArrayLiteral(children) if ctx.mode == HoistingMode::AggregateLiteralLowering => {
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
                  expression: Expression::Variable(temp),
                  location,
                  exp_type: ast.expressions[expr].exp_type.clone(),
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
               block.statements.insert(vv.stmt_anchor, assignment);
            }
         }
         _ => {
            let temp_assign = {
               let lhs = ast.expressions.insert(temp_expression_node);
               let rhs = ast.expressions.insert(ExpressionNode {
                  expression: old_expression,
                  exp_type: ast.expressions[expr].exp_type.clone(),
                  location: ast.expressions[expr].location,
               });
               ast.statements.insert(StatementNode {
                  statement: Statement::Assignment(lhs, rhs),
                  location,
               })
            };
            block.statements.insert(vv.stmt_anchor, temp_assign);
         }
      }
   }

   // The same expression id shouldn't appear in the AST twice,
   // so we can simply truncate instead of splitting off as we do for
   // the list of statement block indices
   ctx.pending_hoists.truncate(before_pending_hoists);

   for if_stmt in new_ifs {
      let else_s = {
         let mut the_statement = std::mem::replace(&mut ast.statements[if_stmt].statement, Statement::Break);
         let Statement::IfElse {
            cond: _,
            then: then_b,
            otherwise: else_s,
            constant: _,
         } = &mut the_statement
         else {
            unreachable!()
         };
         let else_s = *else_s;
         vv_block(then_b, ctx, ast);
         ast.statements[if_stmt].statement = the_statement;
         else_s
      };
      {
         let mut the_statement = std::mem::replace(&mut ast.statements[else_s].statement, Statement::Break);
         let Statement::Block(bn) = &mut the_statement else {
            unreachable!()
         };
         vv_block(bn, ctx, ast);
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
         );
         vv_expr(
            *rhs_expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::AssignmentRhs,
         );
      }
      Statement::Block(block) | Statement::Loop(block) => {
         vv_block(block, vv_context, ast);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse {
         cond: if_expr,
         then: if_block,
         otherwise: else_statement,
         constant: _,
      } => {
         vv_expr(
            *if_expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::IfCondition,
         );
         vv_block(if_block, vv_context, ast);
         vv_statement(*else_statement, vv_context, ast, current_statement);
      }
      Statement::Expression(expr) => {
         vv_expr(
            *expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::ExprStmt,
         );
      }
      Statement::Return(expr) => {
         vv_expr(
            *expr,
            vv_context,
            &ast.expressions,
            current_statement,
            ParentCtx::Return,
         );
      }
      Statement::VariableDeclaration { .. } | Statement::For { .. } | Statement::While(_, _) | Statement::Defer(_) => {
         unreachable!()
      }
   }
   ast.statements[statement].statement = the_statement;
}

#[derive(PartialEq, Clone, Copy)]
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
) {
   match &expressions[expr_index].expression {
      Expression::ArrayIndex { array, index } => {
         vv_expr(*array, ctx, expressions, current_stmt, ParentCtx::Expr);
         vv_expr(*index, ctx, expressions, current_stmt, ParentCtx::Expr);
      }
      Expression::ProcedureCall { args, proc_expr } => {
         vv_expr(*proc_expr, ctx, expressions, current_stmt, ParentCtx::Expr);

         for arg in args.iter() {
            vv_expr(arg.expr, ctx, expressions, current_stmt, ParentCtx::Expr);
         }
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         vv_expr(*lhs, ctx, expressions, current_stmt, ParentCtx::Expr);
         vv_expr(*rhs, ctx, expressions, current_stmt, ParentCtx::Expr);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for expr in field_exprs.values().flatten().copied() {
            vv_expr(expr, ctx, expressions, current_stmt, ParentCtx::Expr);
         }
      }
      Expression::FieldAccess(_, expr) | Expression::UnaryOperator(_, expr) | Expression::Cast { expr, .. } => {
         vv_expr(*expr, ctx, expressions, current_stmt, ParentCtx::Expr);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter().copied() {
            vv_expr(expr, ctx, expressions, current_stmt, ParentCtx::Expr);
         }
      }
      Expression::IfX(a, b, c) => {
         // IfX is hoisted specially, because it needs to become an if statement.
         // We still need to visit our children to see if we have to hoist this statement,
         // but we don't actually want to hoist B/C because that tree will be hoisted to the wrong spot
         // So what we do is we descend into B/C to allow for marking "this statement needs to be hoisted"
         // but then we pretend it didn't happen. Then, during hoisting we descend into the consequent/else
         // blocks that we create to do the marking and hoisting. Simple.
         vv_expr(*a, ctx, expressions, current_stmt, ParentCtx::Expr);
         let before_len = ctx.exprs_to_hoist.len();
         let before_marked = ctx.pending_hoists.len();
         vv_expr(*b, ctx, expressions, current_stmt, ParentCtx::Expr);
         vv_expr(*c, ctx, expressions, current_stmt, ParentCtx::Expr);
         ctx.exprs_to_hoist.truncate(before_len);
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
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }

   match ctx.mode {
      HoistingMode::AggregateLiteralLowering => match &expressions[expr_index].expression {
         Expression::StringLiteral(_) | Expression::StructLiteral(_, _) | Expression::ArrayLiteral(_) => {
            ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
         }
         Expression::IfX(_, _, _) => {
            ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::IfOtherHoisting);
         }
         Expression::ProcedureCall { .. } => {
            let exp_type = expressions[expr_index].exp_type.as_ref().unwrap();

            if parent_ctx == ParentCtx::Expr {
               let reason = if exp_type.is_aggregate() {
                  // The point here is that we need to hoist calls where an aggregate is returned, because currently
                  // a returned aggregate is an address _in the function we just called_, so not hoisting would mean
                  // that we clobber the aggregate if we make another call.
                  HoistReason::Must
               } else {
                  HoistReason::IfOtherHoisting
               };

               ctx.mark_expr_for_hoisting(expr_index, current_stmt, reason);
            }
         }
         _ => (),
      },
      HoistingMode::PreConstantFold => match &expressions[expr_index].expression {
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

            // assumption: procedure call always has side effects
            // If we eventually decide to come up with a list of pure procedure calls, this needs to be updated
            // @PureCalls
            if parent_ctx == ParentCtx::Expr {
               ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::IfOtherHoisting);
            }
         }
         Expression::UnaryOperator(UnOp::AddressOf, expr)
         | Expression::FieldAccess(_, expr)
         | Expression::ArrayIndex { array: expr, .. } => {
            if !expressions[*expr].expression.is_lvalue(expressions, ctx.global_info) {
               ctx.mark_expr_for_hoisting(*expr, current_stmt, HoistReason::Must);
            }
         }
         Expression::IfX(_, _, _) => {
            ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::IfOtherHoisting);
         }
         _ => (),
      },
      HoistingMode::ThreeAddressCode => {
         let is_ifx = matches!(expressions[expr_index].expression, Expression::IfX(_, _, _));
         let is_effective_top_level = (parent_ctx == ParentCtx::AssignmentRhs
            && sizeof_type_mem(
               expressions[expr_index].exp_type.as_ref().unwrap(),
               ctx.user_defined_types,
               Target::Qbe,
            ) == 0)
            || parent_ctx == ParentCtx::ExprStmt;
         let is_var = matches!(expressions[expr_index].expression, Expression::Variable(_));
         let is_var_deref =
            if let Expression::UnaryOperator(UnOp::Dereference, child) = expressions[expr_index].expression {
               matches!(expressions[child].expression, Expression::Variable(_))
            } else {
               false
            };
         let is_literal = is_non_aggregate_const(&expressions[expr_index].expression);
         if is_ifx || (!is_effective_top_level && !is_literal && !is_var && !is_var_deref) {
            ctx.mark_expr_for_hoisting(expr_index, current_stmt, HoistReason::Must);
         }
      }
   }
}
