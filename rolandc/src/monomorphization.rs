use std::collections::HashMap;

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

const DEPTH_LIMIT: usize = 100;

type TemplateWithTypeArguments = (ProcedureId, Box<[ExpressionType]>);

struct SpecializationWorkItem {
   template_with_type_arguments: TemplateWithTypeArguments,
   depth: usize,
}

pub fn monomorphize(program: &mut Program, err_manager: &mut ErrorManager) {
   let mut worklist: Vec<SpecializationWorkItem> = Vec::new();
   let mut new_procedures: HashMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId> = HashMap::new();

   // Construct initial worklist
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

         worklist.push(SpecializationWorkItem {
            template_with_type_arguments: (
               *id,
               generic_args
                  .iter()
                  .map(|x| x.e_type.clone())
                  .collect::<Vec<_>>()
                  .into_boxed_slice(),
            ),
            depth: 0,
         });
      }
   }

   // Specialize procedures (which may add more items to the worklist, variable_replacements)
   while let Some(new_spec) = worklist.pop() {
      if new_procedures.contains_key(&new_spec.template_with_type_arguments) {
         continue;
      }

      let template_procedure = &program.procedures[new_spec.template_with_type_arguments.0];

      // It would be great to do this check before we push it onto the worklist, since at the moment
      // that involes cloning a bunch of types
      let Some(body) = program.procedure_bodies.get(new_spec.template_with_type_arguments.0) else {
         continue;
      };

      if new_spec.depth >= DEPTH_LIMIT {
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
         new_spec.depth,
         &mut program.ast,
         &mut worklist,
         &mut program.next_variable,
      );

      let new_proc_id = program.procedures.insert(cloned_procedure.0);
      program.procedure_bodies.insert(new_proc_id, cloned_procedure.1);

      new_procedures.insert(new_spec.template_with_type_arguments, new_proc_id);
   }

   // Update all procedure calls to refer to specialized procedures
   for expr in program.ast.expressions.values_mut() {
      if let ExpressionType::ProcedureItem(id, generic_args) = expr.exp_type.as_mut().unwrap() {
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
         }
      }
   }
}

fn clone_procedure(
   template_procedure: &ProcedureNode,
   template_body: &ProcedureBody,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   depth: usize,
   ast: &mut AstPool,
   worklist: &mut Vec<SpecializationWorkItem>,
   next_var: &mut VariableId,
) -> (ProcedureNode, ProcedureBody) {
   let mut cloned_proc = template_procedure.clone();
   let mut cloned_body = template_body.clone();

   let mut variable_replacements = HashMap::with_capacity(cloned_body.locals.len());

   // Rewrite locals
   let old_locals = std::mem::take(&mut cloned_body.locals);
   cloned_body.locals.reserve(old_locals.len());
   for (var_id, mut local_type) in old_locals {
      map_generic_to_concrete(&mut local_type, concrete_types, type_parameters);
      variable_replacements.insert(var_id, *next_var);
      cloned_body.locals.insert(*next_var, local_type);
      *next_var = next_var.next();
   }

   // Rewrite the procedure definition
   for param in cloned_proc.definition.parameters.iter_mut() {
      map_generic_to_concrete(&mut param.p_type.e_type, concrete_types, type_parameters);
      param.var_id = variable_replacements[&param.var_id];
   }
   map_generic_to_concrete(
      &mut cloned_proc.definition.ret_type.e_type,
      concrete_types,
      type_parameters,
   );

   deep_clone_block(
      &mut cloned_body.block,
      ast,
      concrete_types,
      type_parameters,
      depth,
      worklist,
      &variable_replacements,
   );

   cloned_proc.definition.type_parameters.clear();

   (cloned_proc, cloned_body)
}

fn deep_clone_block(
   block: &mut BlockNode,
   ast: &mut AstPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   depth: usize,
   worklist: &mut Vec<SpecializationWorkItem>,
   variable_replacements: &HashMap<VariableId, VariableId>,
) {
   for stmt in block.statements.iter_mut() {
      *stmt = deep_clone_stmt(
         *stmt,
         ast,
         concrete_types,
         type_parameters,
         depth,
         worklist,
         variable_replacements,
      );
   }
}

#[must_use]
fn deep_clone_stmt(
   stmt: StatementId,
   ast: &mut AstPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   depth: usize,
   worklist: &mut Vec<SpecializationWorkItem>,
   variable_replacements: &HashMap<VariableId, VariableId>,
) -> StatementId {
   let mut cloned = ast.statements[stmt].clone();
   match &mut cloned.statement {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(
            *lhs,
            &mut ast.expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         *rhs = deep_clone_expr(
            *rhs,
            &mut ast.expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Statement::Block(bn) | Statement::Loop(bn) => {
         deep_clone_block(
            bn,
            ast,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Statement::Continue | Statement::Break => (),
      Statement::IfElse(cond, then, else_s) => {
         *cond = deep_clone_expr(
            *cond,
            &mut ast.expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         deep_clone_block(
            then,
            ast,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         *else_s = deep_clone_stmt(
            *else_s,
            ast,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Statement::Expression(expr) | Statement::Return(expr) => {
         *expr = deep_clone_expr(
            *expr,
            &mut ast.expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Statement::For { .. }
      | Statement::While(_, _)
      | Statement::Defer(_)
      | Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
   }
   ast.statements.insert(cloned)
}

#[must_use]
fn deep_clone_expr(
   expr: ExpressionId,
   expressions: &mut ExpressionPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   depth: usize,
   worklist: &mut Vec<SpecializationWorkItem>,
   variable_replacements: &HashMap<VariableId, VariableId>,
) -> ExpressionId {
   let mut cloned = expressions[expr].clone();
   map_generic_to_concrete(cloned.exp_type.as_mut().unwrap(), concrete_types, type_parameters);
   match &mut cloned.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         *proc_expr = deep_clone_expr(
            *proc_expr,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(
               arg.expr,
               expressions,
               concrete_types,
               type_parameters,
               depth,
               worklist,
               variable_replacements,
            );
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(
               *expr,
               expressions,
               concrete_types,
               type_parameters,
               depth,
               worklist,
               variable_replacements,
            );
         }
      }
      Expression::ArrayIndex { array, index } => {
         *array = deep_clone_expr(
            *array,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         *index = deep_clone_expr(
            *index,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Expression::EnumLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral => (),
      Expression::Variable(var) => {
         if let Some(new_var) = variable_replacements.get(var).copied() {
            *var = new_var;
         }
         // (There won't be a replacement for this variable if it's a global)
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         *lhs = deep_clone_expr(
            *lhs,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         *rhs = deep_clone_expr(
            *rhs,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(
            *operand,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.values_mut().flatten() {
            *field_expr = deep_clone_expr(
               *field_expr,
               expressions,
               concrete_types,
               type_parameters,
               depth,
               worklist,
               variable_replacements,
            );
         }
      }
      Expression::FieldAccess(_, base) => {
         *base = deep_clone_expr(
            *base,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Expression::Cast { target_type, expr, .. } => {
         map_generic_to_concrete(target_type, concrete_types, type_parameters);
         *expr = deep_clone_expr(
            *expr,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Expression::IfX(a, b, c) => {
         *a = deep_clone_expr(
            *a,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         *b = deep_clone_expr(
            *b,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
         *c = deep_clone_expr(
            *c,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
            variable_replacements,
         );
      }
      Expression::BoundFcnLiteral(id, generic_args) => {
         for garg in generic_args.iter_mut() {
            map_generic_to_concrete(&mut garg.e_type, concrete_types, type_parameters);
         }
         if !generic_args.is_empty() {
            worklist.push(SpecializationWorkItem {
               template_with_type_arguments: (
                  *id,
                  generic_args
                     .iter()
                     .map(|x| x.e_type.clone())
                     .collect::<Vec<_>>()
                     .into_boxed_slice(),
               ),
               depth: depth + 1,
            });
         }
      }
      Expression::UnresolvedVariable(_)
      | Expression::UnresolvedProcLiteral(_, _)
      | Expression::UnresolvedStructLiteral(_, _)
      | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
   expressions.insert(cloned)
}
