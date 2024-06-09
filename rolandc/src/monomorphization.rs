use indexmap::{IndexMap, IndexSet};

use crate::interner::StrId;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionPool, ProcedureBody, ProcedureId, ProcedureNode, Statement,
   StatementId, VariableId,
};
use crate::semantic_analysis::validator::map_generic_to_concrete;
use crate::type_data::ExpressionType;
use crate::Program;

pub const DEPTH_LIMIT: u64 = 100;

pub fn monomorphize(
   program: &mut Program,
   specialized_procedures: &mut IndexMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId>,
   specializations_to_create: Vec<(ProcedureId, Box<[ExpressionType]>)>,
) {
   // Specialize procedures
   for new_spec in specializations_to_create {
      if specialized_procedures.contains_key(&new_spec) {
         continue;
      }

      let template_procedure = &program.procedures[new_spec.0];

      // It would be great to do this check before we push it onto the worklist, since at the moment
      // that involves cloning a bunch of types
      let Some(body) = program.procedure_bodies.get(new_spec.0) else {
         continue;
      };

      let cloned_procedure = clone_procedure(
         template_procedure,
         body,
         &new_spec.1,
         &template_procedure.type_parameters,
         &mut program.ast,
      );

      let new_proc_id = program.procedures.insert(cloned_procedure.0);
      program.procedure_bodies.insert(new_proc_id, cloned_procedure.1);

      specialized_procedures.insert(new_spec, new_proc_id);
   }

   // Update all procedure calls to refer to specialized procedures
   for expr in program.ast.expressions.values_mut() {
      if let Some(ExpressionType::ProcedureItem(id, generic_args)) = expr.exp_type.as_mut() {
         if generic_args.is_empty() {
            continue;
         }

         if let Some(new_id) = specialized_procedures.get(&(*id, generic_args.clone())).copied() {
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

         if let Some(new_id) = specialized_procedures.get(&(*id, gargs)).copied() {
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

   deep_clone_block(&mut cloned_body.block, ast);

   cloned_proc.definition.type_parameters.clear();
   cloned_proc.type_parameters.clear();

   cloned_proc.specialized_type_parameters = type_parameters
      .keys()
      .copied()
      .zip(concrete_types.iter().cloned())
      .collect();

   (cloned_proc, cloned_body)
}

fn deep_clone_block(block: &mut BlockNode, ast: &mut AstPool) {
   for stmt in block.statements.iter_mut() {
      *stmt = deep_clone_stmt(*stmt, ast);
   }
}

#[must_use]
fn deep_clone_stmt(stmt: StatementId, ast: &mut AstPool) -> StatementId {
   let mut cloned = ast.statements[stmt].clone();
   match &mut cloned.statement {
      Statement::Assignment(lhs, rhs) => {
         *lhs = deep_clone_expr(*lhs, &mut ast.expressions);
         *rhs = deep_clone_expr(*rhs, &mut ast.expressions);
      }
      Statement::Block(bn) | Statement::Loop(bn) => {
         deep_clone_block(bn, ast);
      }
      Statement::Continue | Statement::Break => (),
      Statement::IfElse(cond, then, else_s) => {
         *cond = deep_clone_expr(*cond, &mut ast.expressions);
         deep_clone_block(then, ast);
         *else_s = deep_clone_stmt(*else_s, ast);
      }
      Statement::Expression(expr) | Statement::Return(expr) => {
         *expr = deep_clone_expr(*expr, &mut ast.expressions);
      }
      Statement::Defer(ds) => {
         *ds = deep_clone_stmt(*ds, ast);
      }
      Statement::VariableDeclaration {
         var_name: _,
         value: val,
         declared_type: _,
         var_id,
         storage: _,
      } => {
         debug_assert!(*var_id == VariableId::first());
         match val {
            crate::parse::DeclarationValue::Expr(e) => {
               *e = deep_clone_expr(*e, &mut ast.expressions);
            }
            crate::parse::DeclarationValue::Uninit | crate::parse::DeclarationValue::None => (),
         }
      }
      Statement::While(e, body) => {
         *e = deep_clone_expr(*e, &mut ast.expressions);
         deep_clone_block(body, ast);
      }
      Statement::For { .. } => unreachable!(),
   }
   ast.statements.insert(cloned)
}

#[must_use]
fn deep_clone_expr(expr: ExpressionId, expressions: &mut ExpressionPool) -> ExpressionId {
   let mut cloned = expressions[expr].clone();
   debug_assert!(cloned.exp_type.is_none());
   match &mut cloned.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         *proc_expr = deep_clone_expr(*proc_expr, expressions);
         for arg in args.iter_mut() {
            arg.expr = deep_clone_expr(arg.expr, expressions);
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter_mut() {
            *expr = deep_clone_expr(*expr, expressions);
         }
      }
      Expression::ArrayIndex { array, index } => {
         *array = deep_clone_expr(*array, expressions);
         *index = deep_clone_expr(*index, expressions);
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
         *lhs = deep_clone_expr(*lhs, expressions);
         *rhs = deep_clone_expr(*rhs, expressions);
      }
      Expression::UnaryOperator(_, operand) => {
         *operand = deep_clone_expr(*operand, expressions);
      }
      Expression::FieldAccess(_, base) => {
         *base = deep_clone_expr(*base, expressions);
      }
      Expression::Cast { expr, .. } => {
         *expr = deep_clone_expr(*expr, expressions);
      }
      Expression::IfX(a, b, c) => {
         *a = deep_clone_expr(*a, expressions);
         *b = deep_clone_expr(*b, expressions);
         *c = deep_clone_expr(*c, expressions);
      }
      Expression::UnresolvedStructLiteral(_, fields, _) => {
         for field in fields.iter_mut() {
            if let Some(e) = &mut field.1 {
               *e = deep_clone_expr(*e, expressions);
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
