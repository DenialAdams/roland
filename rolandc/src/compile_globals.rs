use std::collections::{HashMap, HashSet};

use indexmap::IndexMap;

use crate::constant_folding::{self, FoldingContext};
use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_w_details};
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{Expression, ExpressionId, ExpressionPool, Program};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::SizeInfo;
use crate::source_info::SourceInfo;
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

#[must_use]
fn fold_expr_id(
   expr_id: ExpressionId,
   expressions: &mut ExpressionPool,
   interner: &Interner,
   err_manager: &mut ErrorManager,
) -> u64 {
   let mut fc = FoldingContext {
      error_count: 0,
      expressions,
   };
   constant_folding::try_fold_and_replace_expr(expr_id, err_manager, &mut fc, interner);

   fc.error_count
}

pub fn ensure_statics_const(
   program: &Program,
   expressions: &mut ExpressionPool,
   interner: &mut Interner,
   err_manager: &mut ErrorManager,
) -> u64 {
   let mut static_err_count: u64 = 0;
   for p_static in program.statics.iter().filter(|x| x.value.is_some()) {
      let p_static_expr = &expressions[p_static.value.unwrap()];

      if p_static.static_type != *p_static_expr.exp_type.as_ref().unwrap()
         && !p_static_expr.exp_type.as_ref().unwrap().is_error_type()
      {
         static_err_count += 1;
         let actual_type_str = p_static_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
         rolandc_error_w_details!(
            err_manager,
            &[(p_static.location, "static"), (p_static_expr.location, "expression")],
            "Declared type {} of static `{}` does not match actual expression type {}",
            p_static.static_type.as_roland_type_info(interner),
            interner.lookup(p_static.name.identifier),
            actual_type_str
         );
      }

      if let Some(v) = p_static.value.as_ref() {
         static_err_count += fold_expr_id(*v, expressions, interner, err_manager);
         let v = &expressions[*v];
         if !crate::constant_folding::is_const(&v.expression, expressions) {
            static_err_count += 1;
            rolandc_error_w_details!(
               err_manager,
               &[(p_static.location, "static"), (v.location, "expression")],
               "Value of static `{}` can't be constant folded. Hint: Either simplify the expression, or initialize it yourself on program start.",
               interner.lookup(p_static.name.identifier),
            );
         }
      }
   }

   static_err_count
}

pub fn compile_globals(
   program: &Program,
   expressions: &mut ExpressionPool,
   interner: &mut Interner,
   struct_size_info: &HashMap<StrId, SizeInfo>,
   err_manager: &mut ErrorManager,
) -> u64 {
   // There is an effective second compilation pipeline for constants. This is because:
   // 1) Lowering constants is something we need to do for compilation
   // 2) Constants can form a DAG of dependency, such that we need to lower them in the right order
   // 3) Constants can use sizeof, MY_ARRAY.length (constant time expressions)
   // As a result, we need to completely simplify constant expressions in the correct (DAG) order before we can proceed with the rest of compilation.

   let all_consts: HashMap<StrId, (SourceInfo, ExpressionId)> = program
      .consts
      .iter()
      .map(|x| (x.name.identifier, (x.location, x.value)))
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
      cg_const(c.name.identifier, &mut cg_ctx, err_manager);
   }

   cg_ctx.error_count
}

fn cg_const(c_name: StrId, cg_context: &mut CgContext, err_manager: &mut ErrorManager) {
   if cg_context.const_replacements.contains_key(&c_name) {
      return;
   }

   cg_context.consts_being_processed.insert(c_name);

   let c = cg_context.all_consts[&c_name];
   cg_expr(c.1, cg_context, err_manager);

   cg_context.error_count += fold_expr_id(c.1, cg_context.expressions, cg_context.interner, err_manager);

   let p_const_expr = &cg_context.expressions[c.1];

   if !crate::constant_folding::is_const(&p_const_expr.expression, cg_context.expressions) {
      cg_context.error_count += 1;
      rolandc_error_w_details!(
         err_manager,
         &[(c.0, "const"), (p_const_expr.location, "expression")],
         "Value of const `{}` can't be constant folded. Hint: Either simplify the expression, or turn the constant into a static and initialize it on program start.",
         cg_context.interner.lookup(c_name)
      );
   }

   cg_context.consts_being_processed.remove(&c_name);
   cg_context.const_replacements.insert(c_name, c.1);
}

fn cg_expr(expr_index: ExpressionId, cg_context: &mut CgContext, err_manager: &mut ErrorManager) {
   // SAFETY: it's paramount that this pointer stays valid, so we can't let the expression array resize
   // while this pointer is alive. We don't do this, because we update this expression in place.
   let expr_to_fold = std::ptr::addr_of!(cg_context.expressions[expr_index]);

   match unsafe { &(*expr_to_fold).expression } {
      Expression::Variable(x) => {
         if cg_context.consts_being_processed.contains(&x.identifier) {
            cg_context.error_count += 1;
            let loc = cg_context.all_consts[&x.identifier].0;
            rolandc_error!(
               err_manager,
               loc,
               "const `{}` has a cyclic dependency",
               cg_context.interner.lookup(x.identifier),
            );
         } else if cg_context.const_replacements.contains_key(&x.identifier) {
            // We've already visited this constant, great, nothing to do
         } else if cg_context.all_consts.contains_key(&x.identifier) {
            cg_const(x.identifier, cg_context, err_manager);
         }
      }
      Expression::ArrayIndex { array, index } => {
         cg_expr(*array, cg_context, err_manager);
         cg_expr(*index, cg_context, err_manager);
      }
      Expression::ProcedureCall { args, .. } => {
         for arg in args.iter() {
            cg_expr(arg.expr, cg_context, err_manager);
         }
      }
      Expression::BinaryOperator {
         operator: _operator,
         lhs,
         rhs,
      } => {
         cg_expr(*lhs, cg_context, err_manager);
         cg_expr(*rhs, cg_context, err_manager);
      }
      Expression::UnaryOperator(_op, expr) => {
         cg_expr(*expr, cg_context, err_manager);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter() {
            cg_expr(*expr, cg_context, err_manager);
         }
      }
      Expression::FieldAccess(_field_names, expr) => {
         cg_expr(*expr, cg_context, err_manager);
      }
      Expression::Cast { expr, .. } => {
         cg_expr(*expr, cg_context, err_manager);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            cg_expr(*expr, cg_context, err_manager);
         }
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
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
