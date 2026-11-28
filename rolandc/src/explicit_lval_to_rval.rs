use crate::Program;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionNode, ExpressionPool, Statement, StatementId, UnOp,
};
use crate::type_data::ExpressionType;

pub fn make_lval_to_rval_explicit(program: &mut Program) {
   program.procedure_bodies.values_mut().for_each(|body| {
      do_block(&body.block, &mut body.ast);
   });
   for a_static_expr in program.non_stack_var_info.iter().filter_map(|x| x.1.initializer) {
      do_expr(a_static_expr, &mut program.global_exprs, false);
   }
}

fn do_block(b: &BlockNode, ast: &mut AstPool) {
   for s in b.statements.iter().copied() {
      do_stmt(s, ast);
   }
}

fn do_stmt(s: StatementId, ast: &mut AstPool) {
   let stmt = std::mem::replace(&mut ast.statements[s].statement, Statement::Break);
   match &stmt {
      Statement::Assignment(lhs, rhs) => {
         do_expr(*lhs, &mut ast.expressions, true);
         do_expr(*rhs, &mut ast.expressions, false);
      }
      Statement::Expression(ex) | Statement::Return(ex) => do_expr(*ex, &mut ast.expressions, false),
      Statement::IfElse {
         cond, then, otherwise, ..
      } => {
         do_expr(*cond, &mut ast.expressions, false);
         do_block(then, ast);
         do_stmt(*otherwise, ast);
      }
      Statement::Block(bn) | Statement::Loop(bn) => do_block(bn, ast),
      Statement::Continue | Statement::Break => (),
      Statement::For { .. } | Statement::While(_, _) | Statement::VariableDeclaration { .. } | Statement::Defer(_) => {
         unreachable!()
      }
   }
   ast.statements[s].statement = stmt;
}

fn do_expr(e: ExpressionId, ast: &mut ExpressionPool, is_lhs_context: bool) {
   let expr_location = ast[e].location;
   let mut the_expr = std::mem::replace(&mut ast[e].expression, Expression::UnitLiteral);
   let mut deref_with_rval_child = false;
   // MUST save this before we mutate children (answer can change)
   let expr_is_lhs = the_expr.is_lvalue_disregard_consts(ast);
   match &the_expr {
      Expression::ArrayIndex { array, index } => {
         do_expr(*array, ast, true);
         do_expr(*index, ast, false);
      }
      Expression::UnaryOperator(unop, ex) => {
         deref_with_rval_child = *unop == UnOp::Dereference && !ast[*ex].expression.is_lvalue_disregard_consts(ast);
         do_expr(*ex, ast, *unop == UnOp::AddressOf || *unop == UnOp::Dereference);
      }
      Expression::FieldAccess(_, base) => do_expr(*base, ast, true),
      expr => expr.for_each_child_assuming_resolved(|child| do_expr(child, ast, false)),
   }
   if let Expression::UnaryOperator(UnOp::AddressOf, child_id) = the_expr {
      ast[e].location = ast[child_id].location;
      the_expr = std::mem::replace(&mut ast[child_id].expression, Expression::UnitLiteral);
   } else if deref_with_rval_child {
      if is_lhs_context {
         // make_address()~ = 10 => make_address() = 10
         let Expression::UnaryOperator(UnOp::Dereference, child_id) = the_expr else {
            unreachable!();
         };
         ast[e].location = ast[child_id].location;
         ast[e].exp_type = Some(ExpressionType::Pointer(Box::new(ast[e].exp_type.take().unwrap())));
         the_expr = std::mem::replace(&mut ast[child_id].expression, Expression::UnitLiteral);
      }
   } else if is_lhs_context {
      ast[e].exp_type = Some(ExpressionType::Pointer(Box::new(ast[e].exp_type.take().unwrap())));
   } else if expr_is_lhs {
      let new_child = ast.insert(ExpressionNode {
         expression: the_expr,
         exp_type: Some(ExpressionType::Pointer(Box::new(ast[e].exp_type.clone().unwrap()))),
         location: expr_location,
      });
      the_expr = Expression::UnaryOperator(UnOp::Dereference, new_child);
   }
   ast[e].expression = the_expr;
}
