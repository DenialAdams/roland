use crate::interner::Interner;
use crate::parse::{Expression, ExpressionIndex, ExpressionPool, Program, Statement, StatementNode};
use std::io::Write;

pub fn print_ast_as_html<W: Write>(
   out: &mut W,
   program: &Program,
   interner: &mut Interner,
   expressions: &ExpressionPool,
) {
   writeln!(out, "<ul class=\"tree\">").unwrap();
   writeln!(out, "<li><span>Program</span>").unwrap();
   writeln!(out, "<ul>").unwrap();
   for procedure in program.procedures.iter() {
      let proc_str_name = interner.lookup(procedure.definition.name);
      writeln!(out, "<li><span>proc «{}»</span>", proc_str_name).unwrap();
      writeln!(out, "<ul>").unwrap();
      for statement_node in procedure.block.statements.iter() {
         print_statement(out, statement_node, expressions, interner);
      }
      writeln!(out, "</ul></li>").unwrap();
   }
   writeln!(out, "</ul>").unwrap();
   writeln!(out, "</li>").unwrap();
   writeln!(out, "</ul>").unwrap();
}

fn print_statement<W: Write>(
   out: &mut W,
   statement_node: &StatementNode,
   expressions: &ExpressionPool,
   interner: &mut Interner,
) {
   match &statement_node.statement {
      Statement::Assignment(le, e) => {
         writeln!(out, "<li><span>Assignment</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *le, expressions, interner);
         print_expression(out, *e, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::Block(bn) => {
         writeln!(out, "<li><span>Block</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         for statement in bn.statements.iter() {
            print_statement(out, statement, expressions, interner);
         }
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::For(var, start_expr, end_expr, bn, _) => {
         writeln!(out, "<li><span>For</span>").unwrap();
         writeln!(out, "<li><span>{}</span>", interner.lookup(var.identifier)).unwrap();
         print_expression(out, *start_expr, expressions, interner);
         print_expression(out, *end_expr, expressions, interner);
         for statement in bn.statements.iter() {
            print_statement(out, statement, expressions, interner);
         }
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::Loop(bn) => {
         writeln!(out, "<li><span>Loop</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         for statement in bn.statements.iter() {
            print_statement(out, statement, expressions, interner);
         }
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::Continue => {
         writeln!(out, "<li><span>Continue</span></li>").unwrap();
      }
      Statement::Break => {
         writeln!(out, "<li><span>Break</span></li>").unwrap();
      }
      Statement::Expression(e) => {
         print_expression(out, *e, expressions, interner);
      }
      Statement::IfElse(e, block_1, block_2) => {
         writeln!(out, "<li><span>If-Else</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *e, expressions, interner);
         for statement in block_1.statements.iter() {
            print_statement(out, statement, expressions, interner);
         }
         print_statement(out, block_2, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::Return(e) => {
         writeln!(out, "<li><span>Return</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *e, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::VariableDeclaration(ident, e, _) => {
         writeln!(out, "<li><span>Variable Declaration</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         writeln!(out, "<li><span>{}</span>", interner.lookup(ident.identifier)).unwrap();
         print_expression(out, *e, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
   }
}

fn print_expression<W: Write>(
   out: &mut W,
   expression_index: ExpressionIndex,
   expressions: &ExpressionPool,
   interner: &mut Interner,
) {
   let expression_node = &expressions[expression_index];
   let type_text = match &expression_node.exp_type {
      Some(x) => format!("<br><span class=\"type\">{}</span>", x.as_roland_type_info(interner)),
      None => "".to_string(),
   };
   match &expression_node.expression {
      Expression::UnitLiteral => {
         writeln!(out, "<li><span>(){}</span></li>", type_text).unwrap();
      }
      Expression::BoolLiteral(x) => {
         writeln!(out, "<li><span>{}{}</span></li>", x, type_text).unwrap();
      }
      Expression::IntLiteral(x) => {
         writeln!(out, "<li><span>{}{}</span></li>", x, type_text).unwrap();
      }
      Expression::FloatLiteral(x) => {
         writeln!(out, "<li><span>{}{}</span></li>", x, type_text).unwrap();
      }
      Expression::StringLiteral(x) => {
         writeln!(out, "<li><span>\"{}\"{}</span></li>", interner.lookup(*x), type_text).unwrap();
      }
      Expression::Variable(x) => {
         let var_str = interner.lookup(*x);
         writeln!(out, "<li><span>{}{}</span></li>", var_str, type_text).unwrap();
      }
      Expression::ProcedureCall(x, args) => {
         writeln!(out, "<li><span>{}(){}</span>", interner.lookup(*x), type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         for arg in args.iter() {
            print_expression(out, arg.expr, expressions, interner);
         }
         writeln!(out, "</ul></li>").unwrap()
      }
      Expression::BinaryOperator { operator, lhs, rhs } => {
         writeln!(out, "<li><span>{:?}{}</span>", operator, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *lhs, expressions, interner);
         print_expression(out, *rhs, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::UnaryOperator(un_op, expr) => {
         writeln!(out, "<li><span>{:?}{}</span>", un_op, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *expr, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::Extend(_, expr) => {
         writeln!(out, "<li><span>Extend{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *expr, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::Truncate(_, expr) => {
         writeln!(out, "<li><span>Truncate{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *expr, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::Transmute(_, expr) => {
         writeln!(out, "<li><span>Transmute{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *expr, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::AType(the_type) => {
         let inner_type_text = the_type.as_roland_type_info(interner);
         writeln!(out, "<li><span>(type {}){}</span>", inner_type_text, type_text).unwrap();
      }
      Expression::StructLiteral(type_name, fields) => {
         writeln!(out, "<li><span>{}{}</span>", interner.lookup(*type_name), type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         for field in fields {
            print_expression(out, field.1, expressions, interner);
         }
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::FieldAccess(field, lhs) => {
         writeln!(out, "<li><span>Field Access{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *lhs, expressions, interner);
         writeln!(out, "<li><span>{:?}</span></li>", field).unwrap();
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::ArrayLiteral(exprs) => {
         writeln!(out, "<li><span>Array{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         for exp in exprs.iter() {
            print_expression(out, *exp, expressions, interner);
         }
         writeln!(out, "</ul></li>").unwrap()
      }
      Expression::ArrayIndex { array, index } => {
         writeln!(out, "<li><span>Array Index{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, *array, expressions, interner);
         print_expression(out, *index, expressions, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::EnumLiteral(name, variant) => {
         writeln!(
            out,
            "<li><span>{}::{}{}</span></li>",
            interner.lookup(*name),
            interner.lookup(*variant),
            type_text
         )
         .unwrap();
      }
   }
}
