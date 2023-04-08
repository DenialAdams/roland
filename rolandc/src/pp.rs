use std::io::Write;

use crate::Program;
use crate::interner::Interner;
use crate::parse::{BlockNode, Expression, ExpressionId, ExpressionPool, Statement, VariableId};
use crate::type_data::ExpressionType;

struct PpCtx<'a, W: Write> {
   indentation_level: usize,
   expressions: &'a ExpressionPool,
   interner: &'a Interner,
   output: &'a mut W,
}

impl<W: Write> PpCtx<'_, W> {
   fn indent(&mut self) -> Result<(), std::io::Error> {
      for _ in 0..self.indentation_level {
         write!(self.output, "   ")?;
      }
      Ok(())
   }
}

fn pp<W: Write>(program: &Program, expressions: &ExpressionPool, interner: &Interner, output: &mut W) -> Result<(), std::io::Error> {
   let mut pp_ctx = PpCtx {
      indentation_level: 0,
      expressions,
      interner,
      output,
   };

   for proc in program.procedures.iter() {
      write!(pp_ctx.output, "proc {}(", interner.lookup(proc.definition.name))?;
      for parameter in proc.definition.parameters.iter() {
         if parameter.named {
            write!(pp_ctx.output, "named ")?;
         }
         write!(pp_ctx.output, "{}: ", interner.lookup(parameter.name))?;
         pp_type(&parameter.p_type.e_type, &mut pp_ctx)?;
      }
      write!(pp_ctx.output, ") -> ")?;
      pp_type(&proc.definition.ret_type.e_type, &mut pp_ctx)?;
      pp_block(&proc.block, &mut pp_ctx)?;
   }

   Ok(())
}

fn pp_block<W: Write>(block: &BlockNode, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   writeln!(pp_ctx.output, " {{")?;
   pp_ctx.indentation_level += 1;
   for stmt in block.statements.iter() {
      pp_ctx.indent()?;
      pp_stmt(&stmt.statement, pp_ctx)?;
   }
   pp_ctx.indentation_level -= 1;
   pp_ctx.indent()?;
   writeln!(pp_ctx.output, "}}")?;
   Ok(())
}

fn pp_stmt<W: Write>(stmt: &Statement, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   match stmt {
      Statement::Assignment(lhs, rhs) => {
         pp_expr(*lhs, pp_ctx)?;
         write!(pp_ctx.output, " = ")?;
         pp_expr(*rhs, pp_ctx)?;
      }
      Statement::Block(bn) => {
         pp_block(bn, pp_ctx)?;
      }
      Statement::Loop(bn) => {
         write!(pp_ctx.output, "loop")?;
         pp_block(bn, pp_ctx)?;
      }
      Statement::For(_, start, end, bn, _, var) => {
         write!(pp_ctx.output, "for ")?;
         pp_var(*var, pp_ctx)?;
         write!(pp_ctx.output, " in ")?;
         pp_expr(*start, pp_ctx)?;
         write!(pp_ctx.output, "..")?;
         pp_expr(*end, pp_ctx)?;
         pp_block(bn, pp_ctx)?;
      }
      Statement::Continue => writeln!(pp_ctx.output, "continue;")?,
      Statement::Break => writeln!(pp_ctx.output, "break;")?,
      Statement::Expression(expr) => {
         pp_expr(*expr, pp_ctx)?;
         writeln!(pp_ctx.output, ";")?;
      }
      Statement::IfElse(cond, then, else_e) => {
         write!(pp_ctx.output, "if ")?;
         pp_expr(*cond, pp_ctx)?;
         pp_block(then, pp_ctx)?;
         write!(pp_ctx.output, " else ")?;
         pp_stmt(&else_e.statement, pp_ctx)?;
      }
      Statement::Return(expr) => {
         write!(pp_ctx.output, "return ")?;
         pp_expr(*expr, pp_ctx)?;
         writeln!(pp_ctx.output, ";")?;
      }
      Statement::VariableDeclaration(_, initializer, declared_type, var) => {
         write!(pp_ctx.output, "let ")?;
         pp_var(*var, pp_ctx)?;
         if let Some(dt) = declared_type {
            write!(pp_ctx.output, ": ")?;
            pp_type(&dt.e_type, pp_ctx)?;
         }
         write!(pp_ctx.output, " = ")?;
         if let Some(initializer) = initializer.as_ref() {
            pp_expr(*initializer, pp_ctx)?;
         } else {
            write!(pp_ctx.output, "___")?;
         }
         writeln!(pp_ctx.output, ";")?;
      }
   }
   Ok(())
}

fn pp_expr<W: Write>(expr: ExpressionId, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   let expr = &pp_ctx.expressions[expr];
   match &expr.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         pp_expr(*proc_expr, pp_ctx)?;
         write!(pp_ctx.output, "(")?;
         for arg in args.iter() {
            pp_expr(arg.expr, pp_ctx)?;
            write!(pp_ctx.output, ",")?;
         }
         write!(pp_ctx.output, ")")?;
      }
      Expression::ArrayLiteral(exprs) => {
         write!(pp_ctx.output, "[")?;
         for expr in exprs.iter() {
            pp_expr(*expr, pp_ctx)?;
            write!(pp_ctx.output, ", ")?;
         }
         write!(pp_ctx.output, "]")?;
      }
      Expression::ArrayIndex { array, index } => {
         pp_expr(*array, pp_ctx)?;
         write!(pp_ctx.output, "[")?;
         pp_expr(*index, pp_ctx)?;
         write!(pp_ctx.output, "]")?;
      }
      Expression::BoolLiteral(val) => {
         write!(pp_ctx.output, "{}", val)?;
      }
      Expression::StringLiteral(val) => {
         write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(*val))?;
      }
      Expression::IntLiteral { .. } => {
         // nocheckin
         write!(pp_ctx.output, "{}", 0)?;
      }
      Expression::FloatLiteral(val) => {
         write!(pp_ctx.output, "{}", val)?;
      }
      Expression::UnitLiteral => {
         write!(pp_ctx.output, "()")?;
      }
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::Variable(v) => {
         pp_var(*v, pp_ctx)?;
      }
      Expression::BinaryOperator { lhs, rhs, operator } => {
         pp_expr(*lhs, pp_ctx)?;
         let op_str = match operator {
            crate::parse::BinOp::Add => "+",
            crate::parse::BinOp::Subtract => "-",
            crate::parse::BinOp::Multiply => "*",
            crate::parse::BinOp::Divide => "/",
            crate::parse::BinOp::Remainder => "%",
            crate::parse::BinOp::Equality => "==",
            crate::parse::BinOp::NotEquality => "!=",
            crate::parse::BinOp::GreaterThan => ">",
            crate::parse::BinOp::LessThan => "<",
            crate::parse::BinOp::GreaterThanOrEqualTo => ">=",
            crate::parse::BinOp::LessThanOrEqualTo => "<=",
            crate::parse::BinOp::BitwiseAnd => "&",
            crate::parse::BinOp::BitwiseOr => "|",
            crate::parse::BinOp::BitwiseXor => "^",
            crate::parse::BinOp::BitwiseLeftShift => "<<",
            crate::parse::BinOp::BitwiseRightShift => ">>",
            crate::parse::BinOp::LogicalAnd => "and",
            crate::parse::BinOp::LogicalOr => "or",
         };
         write!(pp_ctx.output, " {} ", op_str)?;
         pp_expr(*rhs, pp_ctx)?;
      }
      Expression::UnaryOperator(operator, operand) => {
         let (prefix, suffix) = match operator {
            crate::parse::UnOp::Negate => ("-", ""),
            crate::parse::UnOp::Complement => ("!", ""),
            crate::parse::UnOp::AddressOf => ("&", ""),
            crate::parse::UnOp::Dereference => ("", "~"),
         };
         write!(pp_ctx.output, "{}", prefix)?;
         pp_expr(*operand, pp_ctx)?;
         write!(pp_ctx.output, "{}", suffix)?;
      }
      Expression::StructLiteral(_, field_exprs) => {
         pp_type(expr.exp_type.as_ref().unwrap(), pp_ctx)?;
         write!(pp_ctx.output, " {{ ",)?;
         for field_expr in field_exprs.iter() {
            write!(pp_ctx.output, "{}: ", pp_ctx.interner.lookup(field_expr.0))?;
            pp_expr(field_expr.1, pp_ctx)?;
            write!(pp_ctx.output, ", ",)?;
         }
         write!(pp_ctx.output, "}}")?;
      }
      Expression::FieldAccess(fields, base) => {
         pp_expr(*base, pp_ctx)?;
         for field in fields.iter().copied() {
            write!(pp_ctx.output, ".{}", pp_ctx.interner.lookup(field))?;
         }
      }
      Expression::Cast {
         target_type,
         expr,
         cast_type,
      } => {
         pp_expr(*expr, pp_ctx)?;
         let op_str = match cast_type {
            crate::parse::CastType::Extend => "extend",
            crate::parse::CastType::Truncate => "truncate",
            crate::parse::CastType::Transmute => "transmute",
         };
         write!(pp_ctx.output, " {} ", op_str)?;
         pp_type(target_type, pp_ctx)?;
      }
      Expression::EnumLiteral(_, variant) => {
         pp_type(expr.exp_type.as_ref().unwrap(), pp_ctx)?;
         write!(pp_ctx.output, "::{}", pp_ctx.interner.lookup(variant.str))?;
      },
      Expression::BoundFcnLiteral(id, generic_args) => {
         write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(id.str))?;
         for generic_arg in generic_args.iter() {
            write!(pp_ctx.output, "$")?;
            pp_type(&generic_arg.gtype, pp_ctx)?;
         }
      }
   }

   Ok(())
}

fn pp_var<W: Write>(var: VariableId, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   // One day this will probably involve the source name of the variable,
   // since we'll need it for DWARF anyway
   write!(pp_ctx.output, "v{}", var.0)
}

fn pp_type<W: Write>(a_type: &ExpressionType, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   write!(
      pp_ctx.output,
      "{}",
      a_type.as_roland_type_info_like_source(pp_ctx.interner)
   )
}
