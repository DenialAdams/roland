use std::collections::{HashMap, HashSet};
use std::io::Write;

use indexmap::IndexMap;

use crate::constant_folding::{self, FoldingContext};
use crate::interner::{Interner, StrId};
use crate::lex::{emit_source_info, emit_source_info_with_description, SourceInfo};
use crate::parse::{Expression, ExpressionId, ExpressionPool, Program};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::SizeInfo;
use crate::various_expression_lowering;

struct CgContext<'a> {
   error_count: u64,
   expressions: &'a mut ExpressionPool,
   all_consts: &'a HashMap<StrId, (SourceInfo, ExpressionId)>,
   consts_being_processed: &'a mut HashSet<StrId>,
   const_replacements: &'a mut HashMap<StrId, ExpressionId>,
   struct_info: &'a IndexMap<StrId, StructInfo>,
   enum_info: &'a IndexMap<StrId, EnumInfo>,
   struct_size_info: &'a HashMap<StrId, SizeInfo>,
   sizeof_id: StrId,
   length_id: StrId,
   interner: &'a Interner,
}

pub fn ensure_statics_const<W: Write>(
   program: &Program,
   expressions: &mut ExpressionPool,
   interner: &mut Interner,
   err_stream: &mut W,
) -> u64 {
   let mut static_err_count: u64 = 0;
   for p_static in program.statics.iter().filter(|x| x.value.is_some()) {
      let p_static_expr = &expressions[p_static.value.unwrap()];

      if p_static.static_type != *p_static_expr.exp_type.as_ref().unwrap()
         && !p_static_expr.exp_type.as_ref().unwrap().is_error_type()
      {
         static_err_count += 1;
         let actual_type_str = p_static_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
         writeln!(
            err_stream,
            "Declared type {} of static `{}` does not match actual expression type {}",
            p_static.static_type.as_roland_type_info(interner),
            interner.lookup(p_static.name.identifier),
            actual_type_str,
         )
         .unwrap();
         emit_source_info_with_description(err_stream, p_static.static_begin_location, "static", interner);
         emit_source_info_with_description(
            err_stream,
            p_static_expr.expression_begin_location,
            "expression",
            interner,
         );
      }

      if let Some(v) = p_static.value.as_ref() {
         constant_folding::try_fold_and_replace_expr(
            *v,
            err_stream,
            &mut FoldingContext {
               error_count: 0,
               expressions,
            },
            interner,
         );
         let v = &expressions[*v];
         if !crate::constant_folding::is_const(&v.expression, expressions) {
            static_err_count += 1;
            writeln!(
               err_stream,
               "Value of static `{}` can't be constant folded. Hint: Either simplify the expression, or initialize it yourself on program start.",
               interner.lookup(p_static.name.identifier),
            )
            .unwrap();
            emit_source_info_with_description(err_stream, p_static.static_begin_location, "static", interner);
            emit_source_info_with_description(err_stream, v.expression_begin_location, "expression", interner);
         }
      }
   }

   static_err_count
}

pub fn compile_globals<W: Write>(
   program: &Program,
   expressions: &mut ExpressionPool,
   interner: &mut Interner,
   struct_size_info: &HashMap<StrId, SizeInfo>,
   err_stream: &mut W,
) -> u64 {
   // There is an effective second compilation pipeline for constants. This is because:
   // 1) Lowering constants is something we need to do for compilation
   // 2) Constants can form a DAG of dependency, such that we need to lower them in the right order
   // 3) Constants can use sizeof, MY_ARRAY.length (constant time expressions)
   // As a result, we need to completely simplify constant expressions in the correct (DAG) order before we can proceed with the rest of compilation.

   let all_consts: HashMap<StrId, (SourceInfo, ExpressionId)> = program
      .consts
      .iter()
      .map(|x| (x.name.identifier, (x.begin_location, x.value)))
      .collect();
   let mut consts_being_processed: HashSet<StrId> = HashSet::new();
   let mut const_replacements: HashMap<StrId, ExpressionId> = HashMap::new();

   let mut cg_ctx = CgContext {
      expressions,
      all_consts: &all_consts,
      consts_being_processed: &mut consts_being_processed,
      const_replacements: &mut const_replacements,
      sizeof_id: interner.intern("sizeof"),
      length_id: interner.intern("length"),
      struct_info: &program.struct_info,
      enum_info: &program.enum_info,
      struct_size_info,
      interner,
      error_count: 0,
   };

   for c in program.consts.iter() {
      cg_const(c.name.identifier, &mut cg_ctx, err_stream);
   }

   cg_ctx.error_count
}

fn cg_const<W: Write>(c_name: StrId, cg_context: &mut CgContext, err_stream: &mut W) {
   if cg_context.const_replacements.contains_key(&c_name) {
      return;
   }

   cg_context.consts_being_processed.insert(c_name);

   let c = cg_context.all_consts[&c_name];
   cg_expr(c.1, cg_context, err_stream);

   constant_folding::try_fold_and_replace_expr(
      c.1,
      err_stream,
      &mut FoldingContext {
         error_count: 0,
         expressions: cg_context.expressions,
      },
      cg_context.interner,
   );

   let p_const_expr = &cg_context.expressions[c.1];

   if !crate::constant_folding::is_const(&p_const_expr.expression, cg_context.expressions) {
      cg_context.error_count += 1;
      writeln!(
         err_stream,
         "Value of const `{}` can't be constant folded. Hint: Either simplify the expression, or turn the constant into a static and initialize it on program start.",
         cg_context.interner.lookup(c_name),
      )
      .unwrap();
      emit_source_info_with_description(err_stream, c.0, "const", cg_context.interner);
      emit_source_info_with_description(
         err_stream,
         p_const_expr.expression_begin_location,
         "expression",
         cg_context.interner,
      );
   }

   cg_context.consts_being_processed.remove(&c_name);
   cg_context.const_replacements.insert(c_name, c.1);
}

fn cg_expr<W: Write>(expr_index: ExpressionId, cg_context: &mut CgContext, err_stream: &mut W) {
   // SAFETY: it's paramount that this pointer stays valid, so we can't let the expression array resize
   // while this pointer is alive. We don't do this, because we update this expression in place.
   let expr_to_fold = std::ptr::addr_of!(cg_context.expressions[expr_index]);

   match unsafe { &(*expr_to_fold).expression } {
      Expression::Variable(x) => {
         if cg_context.consts_being_processed.contains(x) {
            cg_context.error_count += 1;
            writeln!(
               err_stream,
               "const `{}` has a cyclic dependency",
               cg_context.interner.lookup(*x),
            )
            .unwrap();
            let loc = cg_context.all_consts[x].0;
            emit_source_info(err_stream, loc, cg_context.interner);
         } else if cg_context.const_replacements.contains_key(x) {
            // We've already visited this constant, great, nothing to do
         } else if cg_context.all_consts.contains_key(x) {
            cg_const(*x, cg_context, err_stream);
         }
      }
      Expression::ArrayIndex { array, index } => {
         cg_expr(*array, cg_context, err_stream);
         cg_expr(*index, cg_context, err_stream);
      }
      Expression::ProcedureCall { args, .. } => {
         for arg in args.iter() {
            cg_expr(arg.expr, cg_context, err_stream);
         }
      }
      Expression::BinaryOperator {
         operator: _operator,
         lhs,
         rhs,
      } => {
         cg_expr(*lhs, cg_context, err_stream);
         cg_expr(*rhs, cg_context, err_stream);
      }
      Expression::UnaryOperator(_op, expr) => {
         cg_expr(*expr, cg_context, err_stream);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter() {
            cg_expr(*expr, cg_context, err_stream);
         }
      }
      Expression::FieldAccess(_field_names, expr) => {
         cg_expr(*expr, cg_context, err_stream);
      }
      Expression::Extend(_, expr) => {
         cg_expr(*expr, cg_context, err_stream);
      }
      Expression::Truncate(_, expr) => {
         cg_expr(*expr, cg_context, err_stream);
      }
      Expression::Transmute(_, expr) => {
         cg_expr(*expr, cg_context, err_stream);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            cg_expr(*expr, cg_context, err_stream);
         }
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral(_) => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
   }

   various_expression_lowering::lower_single_expression(
      cg_context.expressions,
      expr_index,
      cg_context.const_replacements,
      cg_context.sizeof_id,
      cg_context.length_id,
      cg_context.struct_info,
      cg_context.struct_size_info,
      cg_context.enum_info,
   );
}
