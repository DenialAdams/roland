use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::interner::{Interner, StrId};
use crate::parse::{BlockNode, Expression, ExpressionId, ExpressionPool, ProcedureNode, Statement};
use crate::semantic_analysis::validator::map_generic_to_concrete;
use crate::semantic_analysis::{ProcImplSource, ProcedureInfo};
use crate::type_data::ExpressionType;
use crate::Program;

type ProcedureId = StrId;

type SpecializationWorklist = Vec<(StrId, Box<[ExpressionType]>)>;

pub fn monomorphize(program: &mut Program, expressions: &mut ExpressionPool, interner: &mut Interner) {
   let mut worklist: SpecializationWorklist = Vec::new();
   let mut new_procedures: HashMap<(StrId, Box<[ExpressionType]>), ProcedureId> = HashMap::new();

   // Construct initial worklist
   for expr in expressions.values.iter_mut() {
      if let Expression::BoundFcnLiteral(id, generic_args) = &expr.expression {
         if generic_args.is_empty() {
            continue;
         }

         // This is a call to a generic function inside of a generic function - we'll come back to these.
         if generic_args.iter().any(|x| !x.gtype.is_concrete()) {
            continue;
         }

         worklist.push((
            id.str,
            generic_args
               .iter()
               .map(|x| x.gtype.clone())
               .collect::<Vec<_>>()
               .into_boxed_slice(),
         ));
      }
   }

   // Specialize procedures (which may add more items to the worklist)
   while let Some(new_spec) = worklist.pop() {
      if new_procedures.contains_key(&new_spec) {
         continue;
      }

      let ProcImplSource::ProcedureId(proc_id) = program.procedure_info.get(&new_spec.0).unwrap().proc_impl_source else {
         continue;
      };

      let template_procedure = program.procedures.get(proc_id).unwrap();

      let mut cloned_procedure = clone_procedure(
         template_procedure,
         &new_spec.1,
         program.procedure_info.get(&new_spec.0).unwrap(),
         expressions,
         &mut worklist,
      );
      let new_id = interner.intern(&format!(
         "{}{}",
         interner.lookup(new_spec.0),
         program.procedures.len() - 1
      ));
      cloned_procedure.definition.name = new_id;
      new_procedures.insert(new_spec, new_id);
      program.procedures.push(cloned_procedure);
   }

   // Update all procedure calls to refer to specialized procedures
   for expr in expressions.values.iter_mut() {
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
   expressions: &mut ExpressionPool,
   worklist: &mut SpecializationWorklist,
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
   worklist: &mut SpecializationWorklist,
) {
   for stmt in block.statements.iter_mut() {
      deep_clone_stmt(
         &mut stmt.statement,
         expressions,
         concrete_types,
         type_parameters,
         worklist,
      );
   }
}

fn deep_clone_stmt(
   stmt: &mut Statement,
   expressions: &mut ExpressionPool,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   worklist: &mut SpecializationWorklist,
) {
   match stmt {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(*lhs, expressions, concrete_types, type_parameters, worklist);
         *rhs = deep_clone_expr(*rhs, expressions, concrete_types, type_parameters, worklist);
      }
      Statement::Block(bn) => {
         deep_clone_block(bn, expressions, concrete_types, type_parameters, worklist);
      }
      Statement::Loop(bn) => {
         deep_clone_block(bn, expressions, concrete_types, type_parameters, worklist);
      }
      Statement::For(_, start, end, bn, _, _) => {
         *start = deep_clone_expr(*start, expressions, concrete_types, type_parameters, worklist);
         *end = deep_clone_expr(*end, expressions, concrete_types, type_parameters, worklist);
         deep_clone_block(bn, expressions, concrete_types, type_parameters, worklist);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::Expression(expr) => {
         *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, worklist);
      }
      Statement::IfElse(cond, then, else_e) => {
         *cond = deep_clone_expr(*cond, expressions, concrete_types, type_parameters, worklist);
         deep_clone_block(then, expressions, concrete_types, type_parameters, worklist);
         deep_clone_stmt(
            &mut else_e.statement,
            expressions,
            concrete_types,
            type_parameters,
            worklist,
         );
      }
      Statement::Return(expr) => *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, worklist),
      Statement::VariableDeclaration(_, initializer, declared_type, _) => {
         if let Some(initializer) = initializer.as_mut() {
            *initializer = deep_clone_expr(*initializer, expressions, concrete_types, type_parameters, worklist);
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
   worklist: &mut SpecializationWorklist,
) -> ExpressionId {
   let mut cloned = expressions[expr].clone();
   map_generic_to_concrete(cloned.exp_type.as_mut().unwrap(), concrete_types, type_parameters);
   match &mut cloned.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         *proc_expr = deep_clone_expr(*proc_expr, expressions, concrete_types, type_parameters, worklist);
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(arg.expr, expressions, concrete_types, type_parameters, worklist);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, worklist);
         }
      }
      Expression::ArrayIndex { array, index } => {
         *array = deep_clone_expr(*array, expressions, concrete_types, type_parameters, worklist);
         *index = deep_clone_expr(*index, expressions, concrete_types, type_parameters, worklist);
      }
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::UnitLiteral => (),
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::Variable(_) => (),
      Expression::BinaryOperator { lhs, rhs, .. } => {
         *lhs = deep_clone_expr(*lhs, expressions, concrete_types, type_parameters, worklist);
         *rhs = deep_clone_expr(*rhs, expressions, concrete_types, type_parameters, worklist);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, expressions, concrete_types, type_parameters, worklist);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for field_expr in field_exprs.iter_mut() {
            field_expr.1 = deep_clone_expr(field_expr.1, expressions, concrete_types, type_parameters, worklist);
         }
      }
      Expression::FieldAccess(_, base) => {
         *base = deep_clone_expr(*base, expressions, concrete_types, type_parameters, worklist);
      }
      Expression::Cast { target_type, expr, .. } => {
         map_generic_to_concrete(target_type, concrete_types, type_parameters);
         *expr = deep_clone_expr(*expr, expressions, concrete_types, type_parameters, worklist);
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoundFcnLiteral(id, generic_args) => {
         for garg in generic_args.iter_mut() {
            map_generic_to_concrete(&mut garg.gtype, concrete_types, type_parameters);
         }
         if !generic_args.is_empty() {
            worklist.push((
               id.str,
               generic_args
                  .iter()
                  .map(|x| x.gtype.clone())
                  .collect::<Vec<_>>()
                  .into_boxed_slice(),
            ));
         }
      }
   }
   expressions.push(cloned)
}
