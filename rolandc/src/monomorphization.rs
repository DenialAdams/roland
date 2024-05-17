use indexmap::{IndexMap, IndexSet};

use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::interner::StrId;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionPool, ProcedureBody, ProcedureId, ProcedureNode, Statement,
   StatementId, VariableId,
};
use crate::semantic_analysis::validator::map_generic_to_concrete;
use crate::type_data::ExpressionType;
use crate::Program;

const DEPTH_LIMIT: u64 = 100;

type TemplateWithTypeArguments = (ProcedureId, Box<[ExpressionType]>);

struct SpecializationWorkItem {
   template_with_type_arguments: TemplateWithTypeArguments,
}

pub fn monomorphize(
   program: &mut Program,
   err_manager: &mut ErrorManager,
   new_procedures: &mut IndexMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId>
) {
   let mut specializations_to_create: Vec<SpecializationWorkItem> = Vec::new();

   for expr in program.ast.expressions.values_mut() {
      if let Expression::BoundFcnLiteral(id, generic_args) = &expr.expression {
         if generic_args.is_empty() {
            continue;
         }

         // This is a call to a generic function inside of a generic function - we'll come back to these.
         if generic_args
            .iter()
            .any(|x| x.e_type.is_or_contains_or_points_to_generic())
         {
            continue;
         }

         specializations_to_create.push(SpecializationWorkItem {
            template_with_type_arguments: (
               *id,
               generic_args
                  .iter()
                  .map(|x| x.e_type.clone())
                  .collect::<Vec<_>>()
                  .into_boxed_slice(),
            ),
         });
      }
   }

   // Specialize procedures
   for new_spec in specializations_to_create {
      if new_procedures.contains_key(&new_spec.template_with_type_arguments) {
         continue;
      }

      let template_procedure = &program.procedures[new_spec.template_with_type_arguments.0];

      // It would be great to do this check before we push it onto the worklist, since at the moment
      // that involves cloning a bunch of types
      let Some(body) = program.procedure_bodies.get(new_spec.template_with_type_arguments.0) else {
         continue;
      };

      if 0 >= DEPTH_LIMIT {
         rolandc_error!(
            err_manager,
            template_procedure.location,
            "Reached depth limit of {} during monomorphization",
            DEPTH_LIMIT
         );

         return;
      }

      let cloned_procedure = clone_procedure(
         template_procedure,
         body,
         &new_spec.template_with_type_arguments.1,
         &template_procedure.type_parameters,
         &mut program.ast,
      );

      let new_proc_id = program.procedures.insert(cloned_procedure.0);
      program.procedure_bodies.insert(new_proc_id, cloned_procedure.1);

      new_procedures.insert(new_spec.template_with_type_arguments, new_proc_id);
   }

   // Update all procedure calls to refer to specialized procedures
   for expr in program.ast.expressions.values_mut() {
      if let Some(ExpressionType::ProcedureItem(id, generic_args)) = expr.exp_type.as_mut() {
         if generic_args.is_empty() {
            continue;
         }

         if let Some(new_id) = new_procedures.get(&(*id, generic_args.clone())).copied() {
            *id = new_id;
         }
      }
      if let Expression::BoundFcnLiteral(id, generic_args) = &mut expr.expression {
         if generic_args.is_empty() {
            continue;
         }

         let gargs = generic_args
            .iter()
            .map(|x| x.e_type.clone())
            .collect::<Vec<_>>()
            .into_boxed_slice();

         if let Some(new_id) = new_procedures.get(&(*id, gargs)).copied() {
            *id = new_id;
            *generic_args = Box::new([]);
         }
      }
   }
}

fn clone_procedure(
   template_procedure: &ProcedureNode,
   template_body: &ProcedureBody,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   ast: &mut AstPool,
) -> (ProcedureNode, ProcedureBody) {
   let mut cloned_proc = template_procedure.clone();
   let mut cloned_body = template_body.clone();

   for param in cloned_proc.definition.parameters.iter_mut() {
      map_generic_to_concrete(&mut param.p_type.e_type, concrete_types, type_parameters);
   }
   map_generic_to_concrete(
      &mut cloned_proc.definition.ret_type.e_type,
      concrete_types,
      type_parameters,
   );

   deep_clone_block(&mut cloned_body.block, ast, concrete_types, type_parameters);

   cloned_proc.definition.type_parameters.clear();
   cloned_proc.type_parameters.clear();

   (cloned_proc, cloned_body)
}

fn deep_clone_block(
   block: &mut BlockNode,
   ast: &mut AstPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
) {
   for stmt in block.statements.iter_mut() {
      *stmt = deep_clone_stmt(*stmt, ast, concrete_types, type_parameters);
   }
}

#[must_use]
fn deep_clone_stmt(
   stmt: StatementId,
   ast: &mut AstPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
) -> StatementId {
   let mut cloned = ast.statements[stmt].clone();
   match &mut cloned.statement {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(*lhs, &mut ast.expressions, concrete_types, type_parameters);
         *rhs = deep_clone_expr(*rhs, &mut ast.expressions, concrete_types, type_parameters);
      }
      Statement::Block(bn) | Statement::Loop(bn) => {
         deep_clone_block(bn, ast, concrete_types, type_parameters);
      }
      Statement::Continue | Statement::Break => (),
      Statement::IfElse(cond, then, else_s) => {
         *cond = deep_clone_expr(*cond, &mut ast.expressions, concrete_types, type_parameters);
         deep_clone_block(then, ast, concrete_types, type_parameters);
         *else_s = deep_clone_stmt(*else_s, ast, concrete_types, type_parameters);
      }
      Statement::Expression(expr) | Statement::Return(expr) => {
         *expr = deep_clone_expr(*expr, &mut ast.expressions, concrete_types, type_parameters);
      }
      Statement::Defer(ds) => {
         *ds = deep_clone_stmt(*ds, ast, concrete_types, type_parameters);
      }
      Statement::VariableDeclaration(_, val, _, var_id) => {
         debug_assert!(*var_id == VariableId::first());
         match val {
            crate::parse::DeclarationValue::Expr(e) => {
               *e = deep_clone_expr(*e, &mut ast.expressions, concrete_types, type_parameters);
            }
            crate::parse::DeclarationValue::Uninit | crate::parse::DeclarationValue::None => (),
         }
      }
      Statement::While(e, body) => {
         *e = deep_clone_expr(*e, &mut ast.expressions, concrete_types, type_parameters);
         deep_clone_block(body, ast, concrete_types, type_parameters);
      }
      Statement::For { .. } => unreachable!(),
   }
   ast.statements.insert(cloned)
}

#[must_use]
fn deep_clone_expr(
   expr: ExpressionId,
   expressions: &mut ExpressionPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
) -> ExpressionId {
   let mut cloned = expressions[expr].clone();
   debug_assert!(cloned.exp_type.is_none());
   match &mut cloned.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         *proc_expr = deep_clone_expr(*proc_expr, expressions, concrete_types, type_parameters);
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(arg.expr, expressions, concrete_types, type_parameters);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters);
         }
      }
      Expression::ArrayIndex { array, index } => {
         *array = deep_clone_expr(*array, expressions, concrete_types, type_parameters);
         *index = deep_clone_expr(*index, expressions, concrete_types, type_parameters);
      }
      Expression::UnresolvedEnumLiteral(_, _)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedVariable(_)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral => (),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         *lhs = deep_clone_expr(*lhs, expressions, concrete_types, type_parameters);
         *rhs = deep_clone_expr(*rhs, expressions, concrete_types, type_parameters);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, expressions, concrete_types, type_parameters);
      }
      Expression::FieldAccess(_, base) => {
         *base = deep_clone_expr(*base, expressions, concrete_types, type_parameters);
      }
      Expression::Cast { target_type, expr, .. } => {
         map_generic_to_concrete(target_type, concrete_types, type_parameters);
         *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters);
      }
      Expression::IfX(a, b, c) => {
         *a = deep_clone_expr(*a, expressions, concrete_types, type_parameters);
         *b = deep_clone_expr(*b, expressions, concrete_types, type_parameters);
         *c = deep_clone_expr(*c, expressions, concrete_types, type_parameters);
      }
      Expression::UnresolvedStructLiteral(_, fields) => {
         for field in fields.iter_mut() {
            if let Some(e) = &mut field.1 {
               *e = deep_clone_expr(*e, expressions, concrete_types, type_parameters);
            }
         }
      }
      // These should not yet be resolved
      Expression::BoundFcnLiteral(_, _)
      | Expression::EnumLiteral(_, _)
      | Expression::StructLiteral(_, _)
      | Expression::Variable(_) => unreachable!(),
   }
   expressions.insert(cloned)
}
