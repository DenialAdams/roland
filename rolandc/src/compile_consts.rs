use std::collections::{HashMap, HashSet};

use slotmap::SlotMap;

use crate::BaseTarget;
use crate::constant_folding::{self, FoldingContext};
use crate::error_handling::ErrorManager;
use crate::error_handling::error_handling_macros::rolandc_error;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, EnumId, Expression, ExpressionId, ProcedureId, ProcedureNode, Program, UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::StorageKind;
use crate::semantic_analysis::type_variables::TypeVariableManager;
use crate::source_info::SourceInfo;

struct CgContext<'a> {
   ast: &'a mut AstPool,
   all_consts: &'a HashMap<VariableId, (SourceInfo, ExpressionId, StrId)>,
   consts_being_processed: HashSet<VariableId>,
   enums_being_processed: HashSet<(EnumId, StrId)>,
   const_replacements: HashMap<VariableId, ExpressionId>,
   procedures: &'a SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &'a UserDefinedTypeInfo,
   type_variables: &'a TypeVariableManager,
   interner: &'a Interner,
   target: BaseTarget,
}

fn fold_expr_id(
   expr_id: ExpressionId,
   err_manager: &mut ErrorManager,
   ast: &mut AstPool,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
   const_replacements: &HashMap<VariableId, ExpressionId>,
   type_variables: &TypeVariableManager,
   interner: &Interner,
   target: BaseTarget,
) {
   use crate::semantic_analysis::type_inference::tree_is_well_typed;
   if !tree_is_well_typed(expr_id, &mut ast.expressions, type_variables) {
      return;
   }
   let mut fc = FoldingContext {
      ast,
      procedures,
      user_defined_types,
      const_replacements,
      current_proc_name: None,
      target,
      templated_types: &HashMap::new(),
   };
   constant_folding::try_fold_and_replace_expr(expr_id, &mut Some(err_manager), &mut fc, interner);
}

#[must_use]
pub fn compile_consts(
   program: &mut Program,
   interner: &Interner,
   err_manager: &mut ErrorManager,
   target: BaseTarget,
   type_variables: &TypeVariableManager,
) -> HashMap<VariableId, ExpressionId> {
   // There is an effective second compilation pipeline for constants. This is because:
   // 1) Lowering constants is something we need to do for compilation
   // 2) Constants can form a DAG of dependency, such that we need to lower them in the right order
   // 3) Constants can use sizeof, MY_ARRAY.length (compile time expressions)
   // As a result, we need to completely simplify constant expressions in the correct (DAG) order before we can proceed with the rest of compilation.

   let all_consts: HashMap<VariableId, (SourceInfo, ExpressionId, StrId)> = program
      .non_stack_var_info
      .iter()
      .filter(|x| x.1.kind == StorageKind::Const)
      .map(|x| (*x.0, (x.1.location, x.1.initializer.unwrap(), x.1.name)))
      .collect();

   let mut cg_ctx = CgContext {
      ast: &mut program.ast,
      procedures: &program.procedures,
      all_consts: &all_consts,
      consts_being_processed: HashSet::new(),
      enums_being_processed: HashSet::new(),
      const_replacements: HashMap::new(),
      user_defined_types: &program.user_defined_types,
      type_variables,
      interner,
      target,
   };

   for c_var_id in program
      .non_stack_var_info
      .iter()
      .filter(|x| x.1.kind == StorageKind::Const)
      .map(|x| *x.0)
   {
      cg_const(c_var_id, &mut cg_ctx, err_manager);
   }

   for (e_id, info) in program.user_defined_types.enum_info.iter() {
      for variant_str in info.variants.keys().copied() {
         cg_enum_literal(e_id, variant_str, &mut cg_ctx, err_manager);
      }
   }

   cg_ctx.const_replacements
}

fn cg_const(c_id: VariableId, cg_context: &mut CgContext, err_manager: &mut ErrorManager) {
   if cg_context.const_replacements.contains_key(&c_id) {
      return;
   }

   if !cg_context.consts_being_processed.insert(c_id) {
      let loc = cg_context.all_consts[&c_id].0;
      let name = cg_context.all_consts[&c_id].2;
      rolandc_error!(
         err_manager,
         loc,
         "const `{}` has a cyclic dependency",
         cg_context.interner.lookup(name),
      );
      return;
   }

   let c = cg_context.all_consts[&c_id];
   cg_expr(c.1, cg_context, err_manager);

   fold_expr_id(
      c.1,
      err_manager,
      cg_context.ast,
      cg_context.procedures,
      cg_context.user_defined_types,
      &cg_context.const_replacements,
      cg_context.type_variables,
      cg_context.interner,
      cg_context.target,
   );

   let p_const_expr = &cg_context.ast.expressions[c.1];

   if crate::constant_folding::is_const(&p_const_expr.expression, &cg_context.ast.expressions) {
      cg_context.const_replacements.insert(c_id, c.1);
   } else {
      rolandc_error!(
         err_manager,
         p_const_expr.location,
         "Value of const `{}` can't be constant folded. Hint: Either simplify the expression, or turn the constant into a static and initialize it on program start.",
         cg_context.interner.lookup(c.2)
      );
   }

   cg_context.consts_being_processed.remove(&c_id);
}

fn cg_enum_literal(e_id: EnumId, variant_str: StrId, cg_context: &mut CgContext, err_manager: &mut ErrorManager) {
   let enum_info = &cg_context.user_defined_types.enum_info[e_id];

   let expression_id = enum_info.values[enum_info.variants.get_index_of(&variant_str).unwrap()].unwrap();
   if crate::constant_folding::is_const(
      &cg_context.ast.expressions[expression_id].expression,
      &cg_context.ast.expressions,
   ) {
      return;
   }

   if !cg_context.enums_being_processed.insert((e_id, variant_str)) {
      /*
      let loc = cg_context.all_consts[&c_id].0;
      let name = cg_context.all_consts[&c_id].2;
      rolandc_error!(
         err_manager,
         loc,
         "const `{}` has a cyclic dependency",
         cg_context.interner.lookup(name),
      ); */
      todo!();
      return;
   }

   cg_expr(expression_id, cg_context, err_manager);

   fold_expr_id(
      expression_id,
      err_manager,
      cg_context.ast,
      cg_context.procedures,
      cg_context.user_defined_types,
      &cg_context.const_replacements,
      cg_context.type_variables,
      cg_context.interner,
      cg_context.target,
   );

   let p_const_expr = &cg_context.ast.expressions[expression_id];

   if !crate::constant_folding::is_const(&p_const_expr.expression, &cg_context.ast.expressions) {
      todo!();
      /*rolandc_error!(
         err_manager,
         p_const_expr.location,
         "Value of const `{}` can't be constant folded. Hint: Either simplify the expression, or turn the constant into a static and initialize it on program start.",
         cg_context.interner.lookup(c.2)
      );*/
   }

   cg_context.enums_being_processed.remove(&(e_id, variant_str));
}

fn cg_expr(expr_index: ExpressionId, cg_context: &mut CgContext, err_manager: &mut ErrorManager) {
   let the_expr = std::mem::replace(
      &mut cg_context.ast.expressions[expr_index].expression,
      Expression::UnitLiteral,
   );
   match &the_expr {
      Expression::IfX(a, b, c) => {
         cg_expr(*a, cg_context, err_manager);
         cg_expr(*b, cg_context, err_manager);
         cg_expr(*c, cg_context, err_manager);
      }
      Expression::Variable(x) => {
         if cg_context.all_consts.contains_key(x) {
            cg_const(*x, cg_context, err_manager);
         }
      }
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
      Expression::ArrayIndex { array, index } => {
         cg_expr(*array, cg_context, err_manager);
         cg_expr(*index, cg_context, err_manager);
      }
      Expression::ProcedureCall { args, proc_expr } => {
         cg_expr(*proc_expr, cg_context, err_manager);
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
         for expr in field_exprs.values().flatten() {
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
      Expression::EnumLiteral(e_id, variant_str) => cg_enum_literal(*e_id, *variant_str, cg_context, err_manager),
      Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral
      | Expression::BoundFcnLiteral(_, _) => (),
   }
   cg_context.ast.expressions[expr_index].expression = the_expr;
}
