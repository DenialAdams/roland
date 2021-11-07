use crate::{interner::StrId, parse::{BlockNode, Expression, ExpressionNode, Program, Statement}};
use std::{collections::HashMap, io::Write};

pub fn lower_consts<W: Write>(program: &mut Program, err_stream: &mut W) {
   let mut const_replacements: HashMap<StrId, ExpressionNode> = HashMap::new();

   for p_const in program.consts.drain(0..) {
      const_replacements.insert(p_const.name, p_const.value);
   }

   for procedure in program.procedures.iter_mut() {
      lower_block(&mut procedure.block, err_stream, &const_replacements);
   }
}

fn lower_block<W: Write>(block: &mut BlockNode, err_stream: &mut W, const_replacements: &HashMap<StrId, ExpressionNode>) {
   for statement in block.statements.iter_mut() {
      lower_statement(&mut statement.statement, err_stream, const_replacements);
   }
}

fn lower_statement<W: Write>(statement: &mut Statement, err_stream: &mut W, const_replacements: &HashMap<StrId, ExpressionNode>) {
   match statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         try_lower_and_replace_expr(lhs_expr, err_stream, const_replacements);
         try_lower_and_replace_expr(rhs_expr, err_stream, const_replacements);
      }
      Statement::Block(block) => {
         lower_block(block, err_stream, const_replacements);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse(if_expr, if_block, else_statement) => {
         try_lower_and_replace_expr(if_expr, err_stream, const_replacements);
         lower_block(if_block, err_stream, const_replacements);
         lower_statement(&mut else_statement.statement, err_stream, const_replacements);
      }
      Statement::For(_var, start_expr, end_expr, block, _) => {
         try_lower_and_replace_expr(start_expr, err_stream, const_replacements);
         try_lower_and_replace_expr(end_expr, err_stream, const_replacements);
         lower_block(block, err_stream, const_replacements);
      }
      Statement::Loop(block) => {
         lower_block(block, err_stream, const_replacements);
      }
      Statement::Expression(expr) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);
      }
      Statement::Return(expr) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);
      }
      Statement::VariableDeclaration(_, expr, _) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);
      }
   }
}

#[must_use]
fn lower_expr<W: Write>(
   expr_to_fold: &mut ExpressionNode,
   err_stream: &mut W,
   const_replacements: &HashMap<StrId, ExpressionNode>,
) -> Option<ExpressionNode> {
   match &mut expr_to_fold.expression {
      Expression::ArrayIndex(array, index) => {
         try_lower_and_replace_expr(array, err_stream, const_replacements);
         try_lower_and_replace_expr(index, err_stream, const_replacements);

         None
      }
      Expression::Variable(x) => {
         const_replacements.get(x).cloned()
      },
      Expression::ProcedureCall(_name, args) => {
         for arg in args.iter_mut() {
            try_lower_and_replace_expr(&mut arg.expr, err_stream, const_replacements);
         }

         None
      }
      Expression::ArrayLiteral(_) => None,
      Expression::BoolLiteral(_) => None,
      Expression::StringLiteral(_) => None,
      Expression::IntLiteral(_) => None,
      Expression::FloatLiteral(_) => None,
      Expression::UnitLiteral => None,
      Expression::BinaryOperator(_, exprs) => {
         try_lower_and_replace_expr(&mut exprs.0, err_stream, const_replacements);
         try_lower_and_replace_expr(&mut exprs.1, err_stream, const_replacements);

         None
      }
      Expression::UnaryOperator(_, expr) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);
         None
      }
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter_mut() {
            try_lower_and_replace_expr(expr, err_stream, const_replacements);
         }

         None
      }
      Expression::FieldAccess(_, expr) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);

         None
      }
      Expression::Extend(_, expr) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);

         None
      }
      Expression::Truncate(_, expr) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);

         None
      }
      Expression::Transmute(_, expr) => {
         try_lower_and_replace_expr(expr, err_stream, const_replacements);

         None
      }
      Expression::EnumLiteral(_, _) => None,
   }
}

fn try_lower_and_replace_expr<W: Write>(
   node: &mut ExpressionNode,
   err_stream: &mut W,
   const_replacements: &HashMap<StrId, ExpressionNode>,
) {
   if let Some(new_node) = lower_expr(node, err_stream, const_replacements) {
      *node = new_node;
   }
}
