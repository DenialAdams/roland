use std::collections::{HashMap, HashSet};

use slotmap::SlotMap;

use crate::constant_folding::{self, FoldingContext};
use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, Expression, ExpressionId, ProcedureId, ProcedureNode, Program, UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::GlobalKind;
use crate::source_info::SourceInfo;
use crate::Target;

struct CgContext<'a> {
   ast: &'a mut AstPool,
   all_consts: &'a HashMap<VariableId, (SourceInfo, ExpressionId, StrId)>,
   consts_being_processed: &'a mut HashSet<VariableId>,
   const_replacements: &'a mut HashMap<VariableId, ExpressionId>,
   procedures: &'a SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &'a UserDefinedTypeInfo,
   interner: &'a Interner,
   target: Target,
}

fn fold_expr_id(
   expr_id: ExpressionId,
   err_manager: &mut ErrorManager,
   ast: &mut AstPool,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   user_defined_types: &UserDefinedTypeInfo,
   const_replacements: &HashMap<VariableId, ExpressionId>,
   interner: &Interner,
   target: Target,
) {
   let mut fc = FoldingContext {
      ast,
      procedures,
      user_defined_types,
      const_replacements,
      current_proc_name: None,
      target,
   };
   constant_folding::try_fold_and_replace_expr(expr_id, err_manager, &mut fc, interner);
}

pub fn compile_consts(program: &mut Program, interner: &Interner, err_manager: &mut ErrorManager, target: Target) {
   // There is an effective second compilation pipeline for constants. This is because:
   // 1) Lowering constants is something we need to do for compilation
   // 2) Constants can form a DAG of dependency, such that we need to lower them in the right order
   // 3) Constants can use sizeof, MY_ARRAY.length (constant time expressions)
   // As a result, we need to completely simplify constant expressions in the correct (DAG) order before we can proceed with the rest of compilation.

   let all_consts: HashMap<VariableId, (SourceInfo, ExpressionId, StrId)> = program
      .global_info
      .iter()
      .filter(|x| x.1.kind == GlobalKind::Const)
      .map(|x| (*x.0, (x.1.location, x.1.initializer.unwrap(), x.1.name)))
      .collect();
   let mut consts_being_processed: HashSet<VariableId> = HashSet::new();
   let mut const_replacements: HashMap<VariableId, ExpressionId> = HashMap::new();

   let mut cg_ctx = CgContext {
      ast: &mut program.ast,
      procedures: &program.procedures,
      all_consts: &all_consts,
      consts_being_processed: &mut consts_being_processed,
      const_replacements: &mut const_replacements,
      user_defined_types: &program.user_defined_types,
      interner,
      target,
   };

   for c_var_id in program
      .global_info
      .iter()
      .filter(|x| x.1.kind == GlobalKind::Const)
      .map(|x| *x.0)
   {
      cg_const(c_var_id, &mut cg_ctx, err_manager);
   }
}

fn cg_const(c_id: VariableId, cg_context: &mut CgContext, err_manager: &mut ErrorManager) {
   if cg_context.const_replacements.contains_key(&c_id) {
      return;
   }

   cg_context.consts_being_processed.insert(c_id);

   let c = cg_context.all_consts[&c_id];
   cg_expr(c.1, cg_context, err_manager);

   fold_expr_id(
      c.1,
      err_manager,
      cg_context.ast,
      cg_context.procedures,
      cg_context.user_defined_types,
      cg_context.const_replacements,
      cg_context.interner,
      cg_context.target,
   );

   let p_const_expr = &cg_context.ast.expressions[c.1];

   if !crate::constant_folding::is_const(&p_const_expr.expression, &cg_context.ast.expressions) {
      rolandc_error!(
         err_manager,
         p_const_expr.location,
         "Value of const `{}` can't be constant folded. Hint: Either simplify the expression, or turn the constant into a static and initialize it on program start.",
         cg_context.interner.lookup(c.2)
      );
   }

   cg_context.consts_being_processed.remove(&c_id);
   cg_context.const_replacements.insert(c_id, c.1);
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
         if cg_context.consts_being_processed.contains(x) {
            let loc = cg_context.all_consts[x].0;
            let name = cg_context.all_consts[x].2;
            rolandc_error!(
               err_manager,
               loc,
               "const `{}` has a cyclic dependency",
               cg_context.interner.lookup(name),
            );
         } else if cg_context.const_replacements.contains_key(x) {
            // We've already visited this constant, great, nothing to do
         } else if cg_context.all_consts.contains_key(x) {
            cg_const(*x, cg_context, err_manager);
         }
      }
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _)
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
      Expression::EnumLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral
      | Expression::BoundFcnLiteral(_, _) => (),
   }
   cg_context.ast.expressions[expr_index].expression = the_expr;
}
