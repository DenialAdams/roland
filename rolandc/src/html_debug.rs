use crate::parse::{Expression, ExpressionNode, Program, Statement};
use std::fs::File;
use std::io::{BufWriter, Write};

const HTML_HEADER: &'static str = "<!DOCTYPE HTML>
<html lang=\"en\">
<head>
  <meta charset=\"utf-8\">
  <title>rolandc AST debug</title>
  <link rel=\"stylesheet\" href=\"./ast.css\">
</head>
<body>";

pub fn print_ast_as_html(program: &Program) {
   let out_f = File::create("ast.html").unwrap();
   let mut out = BufWriter::new(out_f);
   writeln!(out, "{}", HTML_HEADER).unwrap();
   writeln!(out, "<ul class=\"tree\">").unwrap();
   writeln!(out, "<li><span>Program</span>").unwrap();
   writeln!(out, "<ul>").unwrap();
   for procedure in program.procedures.iter() {
      let label = if procedure.pure { "func" } else { "proc" };
      writeln!(out, "<li><span>{} «{}»</span>", label, procedure.name).unwrap();
      writeln!(out, "<ul>").unwrap();
      for statement in procedure.block.statements.iter() {
         print_statement(&mut out, statement);
      }
      writeln!(out, "</ul></li>").unwrap();
   }
   writeln!(out, "</ul>").unwrap();
   writeln!(out, "</li>").unwrap();
   writeln!(out, "</ul>").unwrap();
   writeln!(out, "</body>").unwrap();
   writeln!(out, "</html>").unwrap();
}

fn print_statement(out: &mut BufWriter<File>, statement: &Statement) {
   match statement {
      Statement::ExpressionStatement(e) => {
         print_expression(out, e);
      }
      Statement::AssignmentStatement(ident, e) => {
         writeln!(out, "<li><span>Assignment</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         writeln!(out, "<li><span>{}</span>", ident).unwrap();
         print_expression(out, e);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::VariableDeclaration(ident, e, _) => {
         writeln!(out, "<li><span>Variable Declaration</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         writeln!(out, "<li><span>{}</span>", ident).unwrap();
         print_expression(out, e);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::IfElseStatement(e, block_1, block_2) => {
         writeln!(out, "<li><span>If-Else Statement</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, e);
         for statement in block_1.statements.iter() {
            print_statement(out, statement);
         }
         print_statement(out, block_2);
         writeln!(out, "</ul></li>").unwrap();
      }
      Statement::BlockStatement(bn) => {
         for statement in bn.statements.iter() {
            print_statement(out, statement);
         }
      }
   }
}

fn print_expression(out: &mut BufWriter<File>, expression_node: &ExpressionNode) {
   let type_text = match &expression_node.exp_type {
      Some(x) => format!("<br><span class=\"type\">{}</span>", x.as_roland_type()),
      None => "".to_string(),
   };
   match &expression_node.expression {
      Expression::BoolLiteral(x) => {
         writeln!(out, "<li><span>{}{}</span></li>", x, type_text).unwrap();
      }
      Expression::IntLiteral(x) => {
         writeln!(out, "<li><span>{}{}</span></li>", x, type_text).unwrap();
      }
      Expression::StringLiteral(x) => {
         writeln!(out, "<li><span>\"{}\"{}</span></li>", x, type_text).unwrap();
      }
      Expression::Variable(x) => {
         writeln!(out, "<li><span>{}{}</span></li>", x, type_text).unwrap();
      }
      Expression::ProcedureCall(x, args) => {
         writeln!(out, "<li><span>{}(){}</span>", x, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         for exp in args {
            print_expression(out, &exp);
         }
         writeln!(out, "</ul></li>").unwrap()
      }
      Expression::BinaryOperator(bin_op, operands) => {
         writeln!(out, "<li><span>{:?}{}</span>", bin_op, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, &operands.0);
         print_expression(out, &operands.1);
         writeln!(out, "</ul></li>").unwrap();
      }
      Expression::UnaryOperator(un_op, expr) => {
         writeln!(out, "<li><span>{:?}{}</span>", un_op, type_text).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, &expr);
         writeln!(out, "</ul></li>").unwrap();
      }
   }
}
