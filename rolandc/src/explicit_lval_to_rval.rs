use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionNode, ExpressionPool, Statement, StatementId, UnOp,
};
use crate::type_data::ExpressionType;
use crate::Program;

pub fn make_lval_to_rval_explicit(program: &mut Program) {
   for body in program.procedure_bodies.iter() {
      do_block(&body.1.block, &mut program.ast);
   }
   for a_static_expr in program.non_stack_var_info.iter().filter_map(|x| x.1.initializer) {
      do_expr(a_static_expr, &mut program.ast.expressions, false);
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
   match &the_expr {
      Expression::ProcedureCall { proc_expr, args } => {
         do_expr(*proc_expr, ast, false);
         for arg in args.iter() {
            do_expr(arg.expr, ast, false);
         }
      }
      Expression::ArrayIndex { array, index } => {
         do_expr(*array, ast, true);
         do_expr(*index, ast, false);
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         do_expr(*lhs, ast, false);
         do_expr(*rhs, ast, false);
      }
      Expression::UnaryOperator(unop, ex) => {
         deref_with_rval_child = *unop == UnOp::Dereference && !ast[*ex].expression.is_lvalue_disregard_consts(ast);
         do_expr(*ex, ast, *unop == UnOp::AddressOf || *unop == UnOp::Dereference);
      }
      Expression::FieldAccess(_, base) => do_expr(*base, ast, true),
      Expression::Cast { expr, .. } => {
         do_expr(*expr, ast, false);
      }
      Expression::IfX(a, b, c) => {
         do_expr(*a, ast, false);
         do_expr(*b, ast, false);
         do_expr(*c, ast, false);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter().copied() {
            do_expr(expr, ast, false);
         }
      }
      Expression::StructLiteral(_, exprs) => {
         for expr in exprs.values().flatten().copied() {
            do_expr(expr, ast, false);
         }
      }
      Expression::Variable(_)
      | Expression::EnumLiteral(_, _)
      | Expression::BoundFcnLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral => (),
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _)
      | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
   }
   // !!! TODO !!! this code is mishandling the following IR:
   // x = &y~
   // the & and ~ cancel out semantically pre-explicit-rval-conversion
   // x = y
   // then we should apply explicit rval conversion
   // x~
   // but this is not what happens.
   if let Expression::UnaryOperator(UnOp::AddressOf, child_id) = the_expr {
      ast[e].location = ast[child_id].location;
      the_expr = std::mem::replace(&mut ast[child_id].expression, Expression::UnitLiteral);
   } else if deref_with_rval_child {
      let Expression::UnaryOperator(UnOp::Dereference, child_id) = the_expr else {
         unreachable!();
      };
      ast[e].location = ast[child_id].location;
      the_expr = std::mem::replace(&mut ast[child_id].expression, Expression::UnitLiteral);
   } else if is_lhs_context {
      ast[e].exp_type = Some(ExpressionType::Pointer(Box::new(ast[e].exp_type.take().unwrap())));
   } else if the_expr.is_lvalue_disregard_consts(ast) {
      let new_child = ast.insert(ExpressionNode {
         expression: the_expr,
         exp_type: Some(ExpressionType::Pointer(Box::new(ast[e].exp_type.clone().unwrap()))),
         location: expr_location,
      });
      the_expr = Expression::UnaryOperator(UnOp::Dereference, new_child);
   }
   ast[e].expression = the_expr;
}
