use std::io::Write;

use slotmap::SecondaryMap;

use crate::interner::Interner;
use crate::parse::{AstPool, BlockNode, DeclarationValue, Expression, ExpressionId, ProcImplSource, ProcedureId, Statement, StatementId, UserDefinedTypeInfo, VariableId};
use crate::semantic_analysis::ProcedureInfo;
use crate::type_data::ExpressionType;
use crate::Program;

struct PpCtx<'a, W: Write> {
   indentation_level: usize,
   ast: &'a AstPool,
   procedure_info: &'a SecondaryMap<ProcedureId, ProcedureInfo>,
   interner: &'a Interner,
   user_defined_types: &'a UserDefinedTypeInfo,
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

pub fn pp<W: Write>(program: &Program, interner: &Interner, output: &mut W) -> Result<(), std::io::Error> {
   let mut pp_ctx = PpCtx {
      indentation_level: 0,
      ast: &program.ast,
      interner,
      output,
      procedure_info: &program.procedure_info,
      user_defined_types: &program.user_defined_types,
   };

   for proc in program.procedures.values() {
      let prefix = match proc.proc_impl {
        ProcImplSource::Builtin => "builtin ",
        ProcImplSource::External => "extern ",
        ProcImplSource::Body(_) => "",
      };
      write!(pp_ctx.output, "{}proc {}", prefix, interner.lookup(proc.definition.name.str))?;
      if !proc.definition.generic_parameters.is_empty() {
         write!(pp_ctx.output, "<")?;
         for (i, g_param) in proc.definition.generic_parameters.iter().enumerate() {
            if i != proc.definition.generic_parameters.len() - 1 {
               write!(pp_ctx.output, "{}, ", pp_ctx.interner.lookup(g_param.str))?;
            } else {
               write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(g_param.str))?;
            }
         }
         write!(pp_ctx.output, ">")?;
      }
      write!(pp_ctx.output, "(")?;
      for (i, parameter) in proc.definition.parameters.iter().enumerate() {
         if parameter.named {
            write!(pp_ctx.output, "named ")?;
         }
         write!(pp_ctx.output, "{}: ", interner.lookup(parameter.name))?;
         pp_type(&parameter.p_type.e_type, &mut pp_ctx)?;
         if i != proc.definition.parameters.len() - 1 {
            write!(pp_ctx.output, ", ")?;
         }
      }
      write!(pp_ctx.output, ") -> ")?;
      pp_type(&proc.definition.ret_type.e_type, &mut pp_ctx)?;
      if let ProcImplSource::Body(b) = &proc.proc_impl {
         pp_block(b, &mut pp_ctx)?;   
      } else {
         writeln!(pp_ctx.output, ";")?;
      }
   }

   Ok(())
}

fn pp_block<W: Write>(block: &BlockNode, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   writeln!(pp_ctx.output, " {{")?;
   pp_ctx.indentation_level += 1;
   for stmt in block.statements.iter().copied() {
      pp_ctx.indent()?;
      pp_stmt(stmt, pp_ctx)?;
   }
   pp_ctx.indentation_level -= 1;
   pp_ctx.indent()?;
   writeln!(pp_ctx.output, "}}")?;
   Ok(())
}

fn pp_stmt<W: Write>(stmt: StatementId, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   let stmt = &pp_ctx.ast.statements[stmt];
   match &stmt.statement {
      Statement::Assignment(lhs, rhs) => {
         pp_expr(*lhs, pp_ctx)?;
         write!(pp_ctx.output, " = ")?;
         pp_expr(*rhs, pp_ctx)?;
         writeln!(pp_ctx.output, ";")?;
      }
      Statement::Block(bn) => {
         pp_block(bn, pp_ctx)?;
      }
      Statement::Loop(bn) => {
         write!(pp_ctx.output, "loop")?;
         pp_block(bn, pp_ctx)?;
      }
      Statement::While(cond, bn) => {
         write!(pp_ctx.output, "while ")?;
         pp_expr(*cond, pp_ctx)?;
         pp_block(bn, pp_ctx)?;
      }
      Statement::Defer(stmt) => {
         write!(pp_ctx.output, "defer ")?;
         pp_stmt(*stmt, pp_ctx)?;
      }
      Statement::For { range_start: start, range_end: end, range_inclusive, induction_var: var, body, ..} => {
         write!(pp_ctx.output, "for ")?;
         pp_var(*var, pp_ctx)?;
         write!(pp_ctx.output, " in ")?;
         pp_expr(*start, pp_ctx)?;
         if *range_inclusive {
            write!(pp_ctx.output, "..=")?;
         } else {
            write!(pp_ctx.output, "..")?;   
         }
         write!(pp_ctx.output, "..")?;
         pp_expr(*end, pp_ctx)?;
         pp_block(body, pp_ctx)?;
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
         let display_else = if let Statement::Block(bn) = &pp_ctx.ast.statements[*else_e].statement {
            !bn.statements.is_empty()
         } else {
            true
         };
         if display_else {
            // This indent isn't quite right :)
            pp_ctx.indent()?;
            write!(pp_ctx.output, "else ")?;
            pp_stmt(*else_e, pp_ctx)?;
         }
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
         match initializer {
            DeclarationValue::Expr(e) => {
               write!(pp_ctx.output, " = ")?;
               pp_expr(*e, pp_ctx)?;
            },
            DeclarationValue::Uninit => write!(pp_ctx.output, " = ___")?,
            DeclarationValue::None => (),
        }
         writeln!(pp_ctx.output, ";")?;
      }
   }
   Ok(())
}

fn pp_expr<W: Write>(expr: ExpressionId, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   // Note that printing an expr might not reflect original order of operations.
   let expr = &pp_ctx.ast.expressions[expr];
   match &expr.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         pp_expr(*proc_expr, pp_ctx)?;
         write!(pp_ctx.output, "(")?;
         for (i, arg) in args.iter().enumerate() {
            pp_expr(arg.expr, pp_ctx)?;
            if i != args.len() - 1 {
               write!(pp_ctx.output, ", ")?;
            }
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
         write!(pp_ctx.output, "\"{}\"", pp_ctx.interner.lookup(*val))?;
      }
      Expression::IntLiteral { .. } => {
         // nocheckin
         write!(pp_ctx.output, "{}", 0)?;
      }
      Expression::FloatLiteral(val) => {
         write!(pp_ctx.output, "{}", *val)?;
      }
      Expression::UnitLiteral => {
         write!(pp_ctx.output, "unit()")?;
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
         for (i, field_expr) in field_exprs.iter().enumerate() {
            if let Some(e) = field_expr.1 {
               write!(pp_ctx.output, "{}: ", pp_ctx.interner.lookup(*field_expr.0))?;
               pp_expr(*e, pp_ctx)?;  
            } else {
               write!(pp_ctx.output, "{},", pp_ctx.interner.lookup(*field_expr.0))?;
            }
            if i != field_exprs.len() - 1 {
               write!(pp_ctx.output, ", ",)?;
            }
         }
         write!(pp_ctx.output, " }}")?;
      }
      Expression::FieldAccess(field, base) => {
         pp_expr(*base, pp_ctx)?;
         write!(pp_ctx.output, ".{}", pp_ctx.interner.lookup(*field))?;
      }
      Expression::Cast {
         target_type,
         expr,
         cast_type,
      } => {
         pp_expr(*expr, pp_ctx)?;
         let op_str = match cast_type {
            crate::parse::CastType::As => "as",
            crate::parse::CastType::Transmute => "transmute",
         };
         write!(pp_ctx.output, " {} ", op_str)?;
         pp_type(target_type, pp_ctx)?;
      }
      Expression::EnumLiteral(_, variant) => {
         pp_type(expr.exp_type.as_ref().unwrap(), pp_ctx)?;
         write!(pp_ctx.output, "::{}", pp_ctx.interner.lookup(*variant))?;
      }
      Expression::BoundFcnLiteral(id, generic_args) => {
         let proc_name = pp_ctx.procedure_info[*id].name.str;
         write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(proc_name))?;
         if !generic_args.is_empty() {
            write!(pp_ctx.output, "$<")?;
            for (i, generic_arg) in generic_args.iter().enumerate() {
               pp_type(&generic_arg.e_type, pp_ctx)?;
               if i != generic_args.len() - 1 {
                  write!(pp_ctx.output, ", ")?;
               }
            }
            write!(pp_ctx.output, ">")?;
         }
      }
      Expression::IfX(a, b, c) => {
         write!(pp_ctx.output, "ifx ")?;
         pp_expr(*a, pp_ctx)?;
         write!(pp_ctx.output, " ")?;
         pp_expr(*b, pp_ctx)?;
         write!(pp_ctx.output, " else ")?;
         pp_expr(*c, pp_ctx)?;
      }
      Expression::UnresolvedProcLiteral(_, _) => todo!(),
      Expression::UnresolvedStructLiteral(_, _) => todo!(),
      Expression::UnresolvedEnumLiteral(_, _) => todo!(),
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
      a_type.as_roland_type_info_like_source(pp_ctx.interner, pp_ctx.user_defined_types, pp_ctx.procedure_info)
   )
}
