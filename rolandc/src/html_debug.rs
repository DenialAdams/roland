use crate::interner::Interner;
use crate::parse::{Expression, ExpressionNode, Program, Statement, StatementNode};
use std::io::Write;

pub fn print_ast_as_html<W: Write>(out: &mut W, program: &Program, interner: &mut Interner) {
   writeln!(out, "<ul class=\"tree\">").unwrap();
   writeln!(out, "<li><span>Program</span>").unwrap();
   writeln!(out, "<ul>").unwrap();
   for procedure in program.procedures.iter() {
      let label = if procedure.pure { "func" } else { "proc" };
      let proc_str_name = interner.lookup(procedure.name);
      writeln!(out, "<li><span>{} «{}»</span>", label, proc_str_name).unwrap();
      writeln!(out, "<ul>").unwrap();
      for statement_node in procedure.block.statements.iter() {
         print_statement(out, statement_node, interner);
      }
      writeln!(out, "</ul></li>").unwrap();
   }
   writeln!(out, "</ul>").unwrap();
   writeln!(out, "</li>").unwrap();
   writeln!(out, "</ul>").unwrap();
}

fn print_statement<W: Write>(out: &mut W, statement_node: &StatementNode, interner: &mut Interner) {
   match &statement_node.statement {
      Statement::AssignmentStatement(le, e) => {
         writeln!(out, "<li><span>Assignment</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, le, interner);
         print_expression(out, e, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::BlockStatement(bn) => {
         writeln!(out, "<li><span>Block</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         for statement in bn.statements.iter() {
            print_statement(out, statement, interner);
         }
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::LoopStatement(bn) => {
         writeln!(out, "<li><span>Loop</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         for statement in bn.statements.iter() {
            print_statement(out, statement, interner);
         }
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::ContinueStatement => {
         writeln!(out, "<li><span>Continue</span></li>").unwrap();
      }
      Statement::BreakStatement => {
         writeln!(out, "<li><span>Break</span></li>").unwrap();
      }
      Statement::ExpressionStatement(e) => {
         print_expression(out, e, interner);
      }
      Statement::IfElseStatement(e, block_1, block_2) => {
         writeln!(out, "<li><span>If-Else</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, e, interner);
         for statement in block_1.statements.iter() {
            print_statement(out, statement, interner);
         }
         print_statement(out, block_2, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::ReturnStatement(e) => {
         writeln!(out, "<li><span>Return</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, e, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::VariableDeclaration(ident, e, _) => {
         writeln!(out, "<li><span>Variable Declaration</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         let ident_str = interner.lookup(*ident);
         writeln!(out, "<li><span>{}</span>", ident_str).unwrap();
         print_expression(out, e, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
   }
}

fn print_expression<W: Write>(out: &mut W, expression_node: &ExpressionNode, interner: &mut Interner) {
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
         let str_value = interner.lookup(*x);
         writeln!(out, "<li><span>\"{}\"{}</span></li>", str_value, type_text).unwrap();
      }
      Expression::Variable(x) => {
         let var_str = interner.lookup(*x);
         writeln!(out, "<li><span>{}{}</span></li>", var_str, type_text).unwrap();
      }
      Expression::ProcedureCall(x, args) => {
         let procedure_str = interner.lookup(*x);
         writeln!(out, "<li><span>{}(){}</span>", procedure_str, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         for arg in args.iter() {
            print_expression(out, &arg.expr, interner);
         }
         writeln!(out, "</ul></li>").unwrap()
      }
      Expression::BinaryOperator(bin_op, operands) => {
         writeln!(out, "<li><span>{:?}{}</span>", bin_op, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, &operands.0, interner);
         print_expression(out, &operands.1, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::UnaryOperator(un_op, expr) => {
         writeln!(out, "<li><span>{:?}{}</span>", un_op, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, expr, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::Extend(_, expr) => {
         writeln!(out, "<li><span>Extend{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, expr, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::Truncate(_, expr) => {
         writeln!(out, "<li><span>Truncate{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, expr, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::Transmute(_, expr) => {
         writeln!(out, "<li><span>Transmute{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, expr, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::StructLiteral(type_name, fields) => {
         let type_name_str = interner.lookup(*type_name);
         writeln!(out, "<li><span>{}{}</span>", type_name_str, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         for field in fields {
            print_expression(out, &field.1, interner);
         }
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::FieldAccess(field, lhs) => {
         writeln!(out, "<li><span>Field Access{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, lhs, interner);
         writeln!(out, "<li><span>{:?}</span></li>", field).unwrap();
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::ArrayLiteral(exprs) => {
         writeln!(out, "<li><span>Array{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         for exp in exprs.iter() {
            print_expression(out, exp, interner);
         }
         writeln!(out, "</ul></li>").unwrap()
      }
      Expression::ArrayIndex(array_expr, index_expr) => {
         writeln!(out, "<li><span>Array Index{}</span>", type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, array_expr, interner);
         print_expression(out, index_expr, interner);
         writeln!(out, "</ul></li>").unwrap();
      }
   }
}
