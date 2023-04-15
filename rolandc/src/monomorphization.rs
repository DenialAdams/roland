use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{BlockNode, Expression, ExpressionId, ExpressionPool, ProcedureNode, Statement};
use crate::semantic_analysis::validator::map_generic_to_concrete;
use crate::semantic_analysis::{ProcImplSource, ProcedureInfo};
use crate::type_data::ExpressionType;
use crate::Program;

const DEPTH_LIMIT: usize = 100;

type ProcedureId = StrId;

type TemplateWithTypeArguments = (StrId, Box<[ExpressionType]>);

struct SpecializationWorkItem {
   template_with_type_arguments: TemplateWithTypeArguments,
   depth: usize,
}

pub fn monomorphize(program: &mut Program, interner: &mut Interner, err_manager: &mut ErrorManager) {
   let mut worklist: Vec<SpecializationWorkItem> = Vec::new();
   let mut new_procedures: HashMap<(StrId, Box<[ExpressionType]>), ProcedureId> = HashMap::new();

   // Construct initial worklist
   for expr in program.expressions.values_mut() {
      if let Expression::BoundFcnLiteral(id, generic_args) = &expr.expression {
         if generic_args.is_empty() {
            continue;
         }

         // This is a call to a generic function inside of a generic function - we'll come back to these.
         if generic_args.iter().any(|x| !x.gtype.is_concrete()) {
            continue;
         }

         worklist.push(SpecializationWorkItem {
            template_with_type_arguments: (
               id.str,
               generic_args
                  .iter()
                  .map(|x| x.gtype.clone())
                  .collect::<Vec<_>>()
                  .into_boxed_slice(),
            ),
            depth: 0,
         });
      }
   }

   // Specialize procedures (which may add more items to the worklist)
   while let Some(new_spec) = worklist.pop() {
      if new_procedures.contains_key(&new_spec.template_with_type_arguments) {
         continue;
      }

      let ProcImplSource::ProcedureId(proc_id) = program.procedure_info.get(&new_spec.template_with_type_arguments.0).unwrap().proc_impl_source else {
         continue;
      };

      let template_procedure = program.procedures.get(proc_id).unwrap();

      if new_spec.depth >= DEPTH_LIMIT {
         rolandc_error!(
            err_manager,
            template_procedure.location,
            "Reached depth limit of {} during monomorphization",
            DEPTH_LIMIT
         );
         return;
      }

      let mut cloned_procedure = clone_procedure(
         template_procedure,
         &new_spec.template_with_type_arguments.1,
         program
            .procedure_info
            .get(&new_spec.template_with_type_arguments.0)
            .unwrap(),
         new_spec.depth,
         &mut program.expressions,
         &mut worklist,
      );
      let new_id = interner.intern(&format!(
         "{}${}",
         interner.lookup(new_spec.template_with_type_arguments.0),
         program.procedures.len() - 1
      ));
      cloned_procedure.definition.name = new_id;
      new_procedures.insert(new_spec.template_with_type_arguments, new_id);
      program.procedures.push(cloned_procedure);
   }

   // Update all procedure calls to refer to specialized procedures
   for expr in program.expressions.values_mut() {
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
            .map(|x| x.gtype.clone())
            .collect::<Vec<_>>()
            .into_boxed_slice();

         if let Some(new_id) = new_procedures.get(&(id.str, gargs)).copied() {
            id.str = new_id;
         }
      }
   }
}

fn clone_procedure(
   template_procedure: &ProcedureNode,
   concrete_types: &[ExpressionType],
   procedure_info: &ProcedureInfo,
   depth: usize,
   expressions: &mut ExpressionPool,
   worklist: &mut Vec<SpecializationWorkItem>,
) -> ProcedureNode {
   // There is one major shortcoming with this procedure: VariableIds are not adjusted.
   // This means that the cloned procedure will share the same variable ids as the original.
   // This is currently OK, but feels sketchy long-term.

   let mut cloned = template_procedure.clone();

   deep_clone_block(
      &mut cloned.block,
      expressions,
      concrete_types,
      &procedure_info.type_parameters,
      depth,
      worklist,
   );

   // Rewrite locals
   for local_type in cloned.locals.values_mut() {
      map_generic_to_concrete(local_type, concrete_types, &procedure_info.type_parameters);
   }

   // Rewrite the procedure definition
   for param in cloned.definition.parameters.iter_mut() {
      map_generic_to_concrete(
         &mut param.p_type.e_type,
         concrete_types,
         &procedure_info.type_parameters,
      );
   }
   map_generic_to_concrete(
      &mut cloned.definition.ret_type.e_type,
      concrete_types,
      &procedure_info.type_parameters,
   );
   cloned.definition.generic_parameters.clear();

   cloned
}

fn deep_clone_block(
   block: &mut BlockNode,
   expressions: &mut ExpressionPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   depth: usize,
   worklist: &mut Vec<SpecializationWorkItem>,
) {
   for stmt in block.statements.iter_mut() {
      deep_clone_stmt(
         &mut stmt.statement,
         expressions,
         concrete_types,
         type_parameters,
         depth,
         worklist,
      );
   }
}

fn deep_clone_stmt(
   stmt: &mut Statement,
   expressions: &mut ExpressionPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   depth: usize,
   worklist: &mut Vec<SpecializationWorkItem>,
) {
   match stmt {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(*lhs, expressions, concrete_types, type_parameters, depth, worklist);
         *rhs = deep_clone_expr(*rhs, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Statement::Block(bn) => {
         deep_clone_block(bn, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Statement::Loop(bn) => {
         deep_clone_block(bn, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Statement::For(_, start, end, bn, _, _) => {
         *start = deep_clone_expr(*start, expressions, concrete_types, type_parameters, depth, worklist);
         *end = deep_clone_expr(*end, expressions, concrete_types, type_parameters, depth, worklist);
         deep_clone_block(bn, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::Expression(expr) => {
         *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Statement::IfElse(cond, then, else_e) => {
         *cond = deep_clone_expr(*cond, expressions, concrete_types, type_parameters, depth, worklist);
         deep_clone_block(then, expressions, concrete_types, type_parameters, depth, worklist);
         deep_clone_stmt(
            &mut else_e.statement,
            expressions,
            concrete_types,
            type_parameters,
            depth,
            worklist,
         );
      }
      Statement::Return(expr) => {
         *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Statement::VariableDeclaration(_, initializer, declared_type, _) => {
         if let Some(initializer) = initializer.as_mut() {
            *initializer = deep_clone_expr(
               *initializer,
               expressions,
               concrete_types,
               type_parameters,
               depth,
               worklist,
            );
         }
         if let Some(dt) = declared_type.as_mut() {
            map_generic_to_concrete(&mut dt.e_type, concrete_types, type_parameters);
         }
      }
   }
}

#[must_use]
fn deep_clone_expr(
   expr: ExpressionId,
   expressions: &mut ExpressionPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   depth: usize,
   worklist: &mut Vec<SpecializationWorkItem>,
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
         );
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(arg.expr, expressions, concrete_types, type_parameters, depth, worklist);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, depth, worklist);
         }
      }
      Expression::ArrayIndex { array, index } => {
         *array = deep_clone_expr(*array, expressions, concrete_types, type_parameters, depth, worklist);
         *index = deep_clone_expr(*index, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::Variable(_) => (),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         *lhs = deep_clone_expr(*lhs, expressions, concrete_types, type_parameters, depth, worklist);
         *rhs = deep_clone_expr(*rhs, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.iter_mut() {
            field_expr.1 = deep_clone_expr(
               field_expr.1,
               expressions,
               concrete_types,
               type_parameters,
               depth,
               worklist,
            );
         }
      }
      Expression::FieldAccess(_, base) => {
         *base = deep_clone_expr(*base, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Expression::Cast { target_type, expr, .. } => {
         map_generic_to_concrete(target_type, concrete_types, type_parameters);
         *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, depth, worklist);
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(id, generic_args) => {
         for garg in generic_args.iter_mut() {
            map_generic_to_concrete(&mut garg.gtype, concrete_types, type_parameters);
         }
         if !generic_args.is_empty() {
            worklist.push(SpecializationWorkItem {
               template_with_type_arguments: (
                  id.str,
                  generic_args
                     .iter()
                     .map(|x| x.gtype.clone())
                     .collect::<Vec<_>>()
                     .into_boxed_slice(),
               ),
               depth: depth + 1,
            });
         }
      }
   }
   expressions.insert(cloned)
}
