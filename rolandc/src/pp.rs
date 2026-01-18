use std::io::Write;

use bitvec::boxed::BitBox;
use indexmap::IndexMap;
use slotmap::SlotMap;

use crate::Program;
use crate::backend::linearize::{CfgInstruction, post_order};
use crate::backend::liveness::ProgramIndex;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, BinOp, BlockNode, DeclarationValue, Expression, ExpressionId, ExpressionTypeNode, ProcImplSource, ProcedureBody, ProcedureId, ProcedureNode, Statement, StatementId, UnOp, UserDefinedTypeInfo, VariableId
};
use crate::semantic_analysis::StorageKind;
use crate::type_data::ExpressionType;

struct PpCtx<'a, W: Write> {
   indentation_level: usize,
   ast: &'a AstPool,
   procedures: &'a SlotMap<ProcedureId, ProcedureNode>,
   interner: &'a Interner,
   user_defined_types: &'a UserDefinedTypeInfo,
   output: &'a mut W,
   current_proc_liveness: Option<&'a IndexMap<ProgramIndex, BitBox>>,
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
      procedures: &program.procedures,
      user_defined_types: &program.user_defined_types,
      current_proc_liveness: None,
   };

   for (id, proc) in program.procedures.iter() {
      pp_proc_internal(proc, program.procedure_bodies.get(id), &mut pp_ctx)?;
   }

   Ok(())
}

pub fn pp_proc<W: Write>(
   ast: &AstPool,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   procedure_body: Option<&ProcedureBody>,
   user_defined_types: &UserDefinedTypeInfo,
   proc_id: ProcedureId,
   interner: &Interner,
   output: &mut W,
   liveness: &IndexMap<ProgramIndex, BitBox>,
) -> Result<(), std::io::Error> {
   let mut pp_ctx = PpCtx {
      indentation_level: 0,
      ast,
      interner,
      output,
      procedures,
      user_defined_types,
      current_proc_liveness: Some(liveness),
   };

   pp_proc_internal(&pp_ctx.procedures[proc_id], procedure_body, &mut pp_ctx)?;

   Ok(())
}

fn pp_proc_internal<W: Write>(
   proc: &ProcedureNode,
   proc_body: Option<&ProcedureBody>,
   pp_ctx: &mut PpCtx<W>,
) -> Result<(), std::io::Error> {
   let prefix = match proc.impl_source {
      ProcImplSource::Builtin => "builtin ",
      ProcImplSource::External => "extern ",
      ProcImplSource::Native => "",
   };
   write!(
      pp_ctx.output,
      "{}proc {}",
      prefix,
      pp_ctx.interner.lookup(proc.definition.name.str)
   )?;
   if !proc.definition.type_parameters.is_empty() {
      write!(pp_ctx.output, "<")?;
      for (i, g_param) in proc.definition.type_parameters.iter().enumerate() {
         if i == proc.definition.type_parameters.len() - 1 {
            write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(g_param.str))?;
         } else {
            write!(pp_ctx.output, "{}, ", pp_ctx.interner.lookup(g_param.str))?;
         }
      }
      write!(pp_ctx.output, ">")?;
   }
   write!(pp_ctx.output, "(")?;
   for (i, parameter) in proc.definition.parameters.iter().enumerate() {
      if parameter.named {
         write!(pp_ctx.output, "named ")?;
      }
      write!(pp_ctx.output, "{}: ", pp_ctx.interner.lookup(parameter.name))?;
      pp_type(&parameter.p_type.e_type, pp_ctx)?;
      if i != proc.definition.parameters.len() - 1 {
         write!(pp_ctx.output, ", ")?;
      }
   }
   write!(pp_ctx.output, ") -> ")?;
   pp_type(&proc.definition.ret_type.e_type, pp_ctx)?;
   if let Some(b) = proc_body {
      writeln!(pp_ctx.output)?;
      for local in b.locals.iter() {
         write!(pp_ctx.output, "   %v{}: ", local.0.0)?;
         pp_type(local.1, pp_ctx)?;
         writeln!(pp_ctx.output, ";")?;
      }
      if b.cfg.bbs.is_empty() {
         pp_block(&b.block, pp_ctx)
      } else {
         pp_cfg(b, pp_ctx)
      }
   } else {
      writeln!(pp_ctx.output, ";")
   }
}

fn pp_block<W: Write>(block: &BlockNode, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   writeln!(pp_ctx.output, "{{")?;
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
         write!(pp_ctx.output, "loop ")?;
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
      Statement::For {
         range_start: start,
         range_end: end,
         range_inclusive,
         induction_var: var,
         body,
         ..
      } => {
         write!(pp_ctx.output, "for ")?;
         pp_var(*var, pp_ctx)?;
         write!(pp_ctx.output, " in ")?;
         pp_expr(*start, pp_ctx)?;
         if *range_inclusive {
            write!(pp_ctx.output, "..=")?;
         } else {
            write!(pp_ctx.output, "..")?;
         }
         pp_expr(*end, pp_ctx)?;
         write!(pp_ctx.output, " ")?;
         pp_block(body, pp_ctx)?;
      }
      Statement::Continue => writeln!(pp_ctx.output, "continue;")?,
      Statement::Break => writeln!(pp_ctx.output, "break;")?,
      Statement::Expression(expr) => {
         pp_expr(*expr, pp_ctx)?;
         writeln!(pp_ctx.output, ";")?;
      }
      Statement::IfElse {
         cond,
         then,
         otherwise: else_e,
         constant,
      } => {
         if *constant {
            write!(pp_ctx.output, "when ")?;
         } else {
            write!(pp_ctx.output, "if ")?;
         }
         pp_expr(*cond, pp_ctx)?;
         write!(pp_ctx.output, " ")?;
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
      Statement::VariableDeclaration {
         var_name: _,
         value: initializer,
         declared_type,
         var_id: var,
         storage,
      } => {
         match storage {
            None => write!(pp_ctx.output, "let "),
            Some(StorageKind::Const) => write!(pp_ctx.output, "const "),
            Some(StorageKind::Static) => write!(pp_ctx.output, "static "),
         }?;
         pp_var(*var, pp_ctx)?;
         if let Some(dt) = declared_type {
            write!(pp_ctx.output, ": ")?;
            pp_type(&dt.e_type, pp_ctx)?;
         }
         match initializer {
            DeclarationValue::Expr(e) => {
               write!(pp_ctx.output, " = ")?;
               pp_expr(*e, pp_ctx)?;
            }
            DeclarationValue::Uninit => write!(pp_ctx.output, " = ___")?,
            DeclarationValue::None => (),
         }
         writeln!(pp_ctx.output, ";")?;
      }
   }
   Ok(())
}

fn pp_cfg<W: Write>(body: &ProcedureBody, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   writeln!(pp_ctx.output, " {{")?;
   for (i, bb) in post_order(&body.cfg).iter().rev().enumerate() {
      pp_ctx.indent()?;
      writeln!(pp_ctx.output, ".{}", *bb)?;
      pp_ctx.indentation_level += 1;
      for (j, instr) in body.cfg.bbs[*bb].instructions.iter().enumerate() {
         pp_ctx.indent()?;
         match instr {
            CfgInstruction::Assignment(lhs, rhs) => {
               pp_expr(*lhs, pp_ctx)?;
               write!(pp_ctx.output, " = ")?;
               pp_expr(*rhs, pp_ctx)?;
            }
            CfgInstruction::ConditionalJump(e, pass, fail) => {
               write!(pp_ctx.output, "jnz ")?;
               pp_expr(*e, pp_ctx)?;
               write!(pp_ctx.output, " : {}, {}", pass, fail)?;
            }
            CfgInstruction::Jump(dst) => {
               write!(pp_ctx.output, "jmp {}", dst)?;
            }
            CfgInstruction::Return(e) => {
               write!(pp_ctx.output, "ret ")?;
               pp_expr(*e, pp_ctx)?;
            }
            CfgInstruction::Expression(e) => {
               pp_expr(*e, pp_ctx)?;
            }
            CfgInstruction::Nop => write!(pp_ctx.output, "nop")?,
         }
         if let Some(bits) = pp_ctx.current_proc_liveness.and_then(|x| x.get(&ProgramIndex(i, j))) {
            write!(pp_ctx.output, " | live{{")?;
            for bit in bits.iter_ones() {
               let corresponding_var = *body.locals.get_index(bit).unwrap().0;
               pp_var(corresponding_var, pp_ctx)?;
               write!(pp_ctx.output, ", ")?;
            }
            write!(pp_ctx.output, "}}")?;
         }
         writeln!(pp_ctx.output)?;
      }
      pp_ctx.indentation_level -= 1;
   }
   pp_ctx.indent()?;
   writeln!(pp_ctx.output, "}}")?;
   Ok(())
}

fn pp_expr<W: Write>(expr: ExpressionId, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   // Note that printing an expr might not reflect correct order of operations.
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
         for (i, expr) in exprs.iter().enumerate() {
            pp_expr(*expr, pp_ctx)?;
            if i != exprs.len() - 1 {
               write!(pp_ctx.output, ", ")?;
            }
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
         write!(pp_ctx.output, "\"{}\"", pp_ctx.interner.lookup(*val).escape_default())?;
      }
      Expression::IntLiteral { val, .. } => {
         write!(pp_ctx.output, "{}", val)?;
      }
      Expression::FloatLiteral(val) => {
         write!(pp_ctx.output, "{}", *val)?;
      }
      Expression::UnitLiteral => {
         write!(pp_ctx.output, "unit()")?;
      }
      Expression::Variable(v) => {
         pp_var(*v, pp_ctx)?;
      }
      Expression::BinaryOperator { lhs, rhs, operator } => {
         write!(pp_ctx.output, "(")?;
         pp_expr(*lhs, pp_ctx)?;
         let op_str = match operator {
            BinOp::Add => "+",
            BinOp::Subtract => "-",
            BinOp::Multiply => "*",
            BinOp::Divide => "/",
            BinOp::Remainder => "%",
            BinOp::Equality => "==",
            BinOp::NotEquality => "!=",
            BinOp::GreaterThan => ">",
            BinOp::LessThan => "<",
            BinOp::GreaterThanOrEqualTo => ">=",
            BinOp::LessThanOrEqualTo => "<=",
            BinOp::BitwiseAnd => "&",
            BinOp::BitwiseOr => "|",
            BinOp::BitwiseXor => "^",
            BinOp::BitwiseLeftShift => "<<",
            BinOp::BitwiseRightShift => ">>",
            BinOp::LogicalAnd => "and",
            BinOp::LogicalOr => "or",
         };
         write!(pp_ctx.output, " {} ", op_str)?;
         pp_expr(*rhs, pp_ctx)?;
         write!(pp_ctx.output, ")")?;
      }
      Expression::UnaryOperator(operator, operand) => {
         let (prefix, suffix) = match operator {
            UnOp::Negate => ("-", ""),
            UnOp::Complement => ("!", ""),
            UnOp::AddressOf | UnOp::TakeProcedurePointer => ("&", ""),
            UnOp::Dereference => ("", "~"),
         };
         write!(pp_ctx.output, "{}", prefix)?;
         pp_expr(*operand, pp_ctx)?;
         write!(pp_ctx.output, "{}", suffix)?;
      }
      Expression::StructLiteral(_, field_exprs) => {
         pp_type(expr.exp_type.as_ref().unwrap(), pp_ctx)?;
         pp_struct_initializer(field_exprs.iter().map(|x| (*x.0, *x.1)), field_exprs.len(), pp_ctx)?;
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
      Expression::BoundFcnLiteral(id, type_args) => {
         if let Some(proc_name) = pp_ctx.procedures.get(*id).map(|x| x.definition.name.str) {
            write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(proc_name))?;
         } else {
            write!(pp_ctx.output, "XXX")?;
         }
         pp_type_arguments(type_args, pp_ctx)?;
      }
      Expression::IfX(a, b, c) => {
         write!(pp_ctx.output, "ifx ")?;
         pp_expr(*a, pp_ctx)?;
         write!(pp_ctx.output, " ")?;
         pp_expr(*b, pp_ctx)?;
         write!(pp_ctx.output, " else ")?;
         pp_expr(*c, pp_ctx)?;
      }
      Expression::UnresolvedVariable(var_name) => {
         write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(var_name.str))?;
      }
      Expression::UnresolvedProcLiteral(proc_name, type_args) => {
         write!(pp_ctx.output, "{}", pp_ctx.interner.lookup(proc_name.str))?;
         pp_type_arguments(type_args, pp_ctx)?;
      }
      Expression::UnresolvedStructLiteral(etn, fields, _) => {
         pp_type(&etn.e_type, pp_ctx)?;
         pp_struct_initializer(fields.iter().copied(), fields.len(), pp_ctx)?;
      }
      Expression::UnresolvedEnumLiteral(_, _) => unimplemented!(),
   }

   Ok(())
}

fn pp_struct_initializer<W: Write, I: IntoIterator<Item=(StrId, Option<ExpressionId>)>>(field_exprs: I, field_exprs_len: usize, pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   write!(pp_ctx.output, " {{ ",)?;
   for (i, field_expr) in field_exprs.into_iter().enumerate() {
      if let Some(e) = field_expr.1 {
         write!(pp_ctx.output, "{}: ", pp_ctx.interner.lookup(field_expr.0))?;
         pp_expr(e, pp_ctx)?;
      } else {
         write!(pp_ctx.output, "{},", pp_ctx.interner.lookup(field_expr.0))?;
      }
      if i != field_exprs_len - 1 {
         write!(pp_ctx.output, ", ",)?;
      }
   }
   write!(pp_ctx.output, " }}")
}

fn pp_type_arguments<W: Write>(type_args: &[ExpressionTypeNode], pp_ctx: &mut PpCtx<W>) -> Result<(), std::io::Error> {
   if !type_args.is_empty() {
      write!(pp_ctx.output, "$<")?;
      for (i, type_arg) in type_args.iter().enumerate() {
         pp_type(&type_arg.e_type, pp_ctx)?;
         if i != type_args.len() - 1 {
            write!(pp_ctx.output, ", ")?;
         }
      }
      write!(pp_ctx.output, ">")?;
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
      a_type.as_roland_type_info_like_source(pp_ctx.interner, pp_ctx.user_defined_types)
   )
}
