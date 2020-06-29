use crate::parse::{Program, Statement, Expression};
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
      writeln!(out, "<li><span>Procedure «{}»</span>", procedure.name).unwrap();
      writeln!(out, "<ul>").unwrap();
      for statement in procedure.block.statements.iter() {
         print_statement(&mut out, statement);
      }
      writeln!(out, "</ul>").unwrap();
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
   }
}

fn print_expression(out: &mut BufWriter<File>, expression: &Expression) {
   match expression {
      Expression::Int(x) => {
         writeln!(out, "<li><span>{}</span>", x).unwrap();
      }
      Expression::Variable(x) => {
         writeln!(out, "<li><span>{}</span>", x).unwrap();
      }
      Expression::ProcedureCall(x) => {
         writeln!(out, "<li><span>{}()</span>", x).unwrap();
      }
      Expression::BinaryOperator(bin_op, operands) => {
         writeln!(out, "<li><span>{:?}</span>", bin_op).unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, &operands.0);
         print_expression(out, &operands.1);
         writeln!(out, "</ul>").unwrap();
      }
      Expression::Negate(expr) => {
         writeln!(out, "<li><span>Negation</span>").unwrap();
         writeln!(out, "<ul>").unwrap();
         print_expression(out, expr);
         writeln!(out, "</ul>").unwrap();
      }
   }
}
