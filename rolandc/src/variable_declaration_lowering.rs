use indexmap::IndexMap;

use crate::parse::{
   AstPool, BlockNode, DeclarationValue, Expression, ExpressionNode, Statement, StatementId, VariableId,
};
use crate::type_data::ExpressionType;
use crate::Program;

pub fn lower_variable_decls(program: &mut Program) {
   for proc_body in program.procedure_bodies.values_mut() {
      lower_block(&mut proc_body.block, &mut program.ast, &proc_body.locals);
   }
}

fn lower_block(bn: &mut BlockNode, ast: &mut AstPool, locals: &IndexMap<VariableId, ExpressionType>) {
   bn.statements.retain(|stmt| lower_stmt(*stmt, ast, locals));
}

fn lower_stmt(s: StatementId, ast: &mut AstPool, locals: &IndexMap<VariableId, ExpressionType>) -> bool {
   let mut the_statement = std::mem::replace(&mut ast.statements[s].statement, Statement::Break);
   let retain = match &mut the_statement {
      Statement::VariableDeclaration(str_node, dv, _, var) => {
         if let DeclarationValue::Expr(rhs) = dv {
            let lhs_type = locals.get(var).cloned();
            let lhs = ast.expressions.insert(ExpressionNode {
               expression: Expression::Variable(*var),
               exp_type: lhs_type,
               location: str_node.location,
            });
            the_statement = Statement::Assignment(lhs, *rhs);
            true
         } else {
            false
         }
      }
      Statement::IfElse(_, b_then, s_else) => {
         lower_block(b_then, ast, locals);
         lower_stmt(*s_else, ast, locals);
         true
      }
      Statement::Block(bn) | Statement::Loop(bn) | Statement::For { body: bn, .. } | Statement::While(_, bn) => {
         lower_block(bn, ast, locals);
         true
      }
      _ => true,
   };
   ast.statements[s].statement = the_statement;
   retain
}
