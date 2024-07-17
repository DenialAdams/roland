use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::interner::StrId;
use crate::parse::{
   AstPool, BlockNode, Expression, ExpressionId, ExpressionPool, ProcedureBody, ProcedureId, ProcedureNode, Statement,
   StatementId, StructId, UnionId, UserDefinedTypeId, UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::validator::map_generic_to_concrete;
use crate::semantic_analysis::{StructInfo, UnionInfo};
use crate::size_info::{calculate_struct_size_info, calculate_union_size_info};
use crate::type_data::ExpressionType;
use crate::{Program, Target};

pub const DEPTH_LIMIT: u64 = 100;

pub fn monomorphize(
   program: &mut Program,
   specialized_procedures: &mut IndexMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId>,
   specializations_to_create: Vec<(ProcedureId, Box<[ExpressionType]>)>,
) {
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
}

pub fn update_expressions_to_point_to_monomorphized_procedures(
   program: &mut Program,
   specialized_procedures: &IndexMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId>,
) {
   fn lower_type(
      et: &mut ExpressionType,
      specialized_procedures: &IndexMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId>,
   ) {
      if let ExpressionType::ProcedureItem(id, generic_args) = et {
         if generic_args.is_empty() {
            return;
         }

         if let Some(new_id) = specialized_procedures.get(&(*id, generic_args.clone())).copied() {
            *id = new_id;
         }
      }
   }
   for body in program.procedure_bodies.values_mut() {
      for var_type in body.locals.values_mut() {
         lower_type(var_type, specialized_procedures);
      }
   }
   for expr in program.ast.expressions.values_mut() {
      if let Some(et) = expr.exp_type.as_mut() {
         lower_type(et, specialized_procedures);
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

pub fn monomorphize_types(program: &mut Program, target: Target) {
   fn lower_type(
      e: &mut ExpressionType,
      udt: &mut UserDefinedTypeInfo,
      tt: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
      target: Target,
      already_lowered: &mut HashMap<(UserDefinedTypeId, Box<[ExpressionType]>), UserDefinedTypeId>,
   ) {
      match e {
         ExpressionType::Unknown(_)
         | ExpressionType::CompileError
         | ExpressionType::Unresolved { .. }
         | ExpressionType::GenericParam(_) => {
            unreachable!()
         }
         ExpressionType::Never
         | ExpressionType::Enum(_)
         | ExpressionType::Int(_)
         | ExpressionType::Float(_)
         | ExpressionType::Bool
         | ExpressionType::Unit => (),
         ExpressionType::Struct(s_id, type_arguments) => {
            if type_arguments.is_empty() {
               return;
            }

            // sad clone...
            if let Some(lowered_sid) = already_lowered.get(&(UserDefinedTypeId::Struct(*s_id), type_arguments.clone()))
            {
               *s_id = match lowered_sid {
                  UserDefinedTypeId::Struct(x) => *x,
                  _ => unreachable!(),
               };
               *type_arguments = Box::new([]);
            } else {
               let template_si = udt.struct_info.get(*s_id).unwrap();

               let new_location = template_si.location;
               let new_name = template_si.name;
               let mut new_field_types = template_si.field_types.clone();
               let new_sid = udt.struct_info.insert(StructInfo {
                  size: None,
                  location: new_location,
                  name: new_name,
                  field_types: IndexMap::new(),
               });

               // plant the flag first to avoid infinte recursion
               already_lowered.insert(
                  (UserDefinedTypeId::Struct(*s_id), type_arguments.clone()),
                  UserDefinedTypeId::Struct(new_sid),
               );

               for new_ft in new_field_types.iter_mut() {
                  map_generic_to_concrete(
                     &mut new_ft.1.e_type,
                     type_arguments,
                     &tt[&UserDefinedTypeId::Struct(*s_id)],
                  );
                  lower_type(&mut new_ft.1.e_type, udt, tt, target, already_lowered);
               }
               udt.struct_info[new_sid].field_types = new_field_types;

               *s_id = new_sid;
               *type_arguments = Box::new([]);

               calculate_struct_size_info(*s_id, udt, target, tt);
            }
         }
         ExpressionType::Union(u_id, type_arguments) => {
            if type_arguments.is_empty() {
               return;
            }

            // sad clone...
            if let Some(lowered_uid) = already_lowered.get(&(UserDefinedTypeId::Union(*u_id), type_arguments.clone())) {
               *u_id = match lowered_uid {
                  UserDefinedTypeId::Union(x) => *x,
                  _ => unreachable!(),
               };
               *type_arguments = Box::new([]);
            } else {
               let template_ui = udt.union_info.get(*u_id).unwrap();

               let new_location = template_ui.location;
               let new_name = template_ui.name;
               let mut new_field_types = template_ui.field_types.clone();
               let new_uid = udt.union_info.insert(UnionInfo {
                  size: None,
                  location: new_location,
                  name: new_name,
                  field_types: IndexMap::new(),
               });

               // plant the flag first to avoid infinte recursion
               already_lowered.insert(
                  (UserDefinedTypeId::Union(*u_id), type_arguments.clone()),
                  UserDefinedTypeId::Union(new_uid),
               );

               for new_ft in new_field_types.iter_mut() {
                  map_generic_to_concrete(
                     &mut new_ft.1.e_type,
                     type_arguments,
                     &tt[&UserDefinedTypeId::Union(*u_id)],
                  );
                  lower_type(&mut new_ft.1.e_type, udt, tt, target, already_lowered);
               }
               udt.union_info[new_uid].field_types = new_field_types;

               *u_id = new_uid;
               *type_arguments = Box::new([]);

               calculate_union_size_info(*u_id, udt, target, tt);
            }
         }
         ExpressionType::Array(base_type, _) | ExpressionType::Pointer(base_type) => {
            lower_type(base_type, udt, tt, target, already_lowered);
         }
         ExpressionType::ProcedureItem(_, type_arguments) => {
            for a in type_arguments.iter_mut() {
               lower_type(a, udt, tt, target, already_lowered);
            }
         }
         ExpressionType::ProcedurePointer { parameters, ret_type } => {
            for p in parameters.iter_mut() {
               lower_type(p, udt, tt, target, already_lowered);
            }
            lower_type(ret_type, udt, tt, target, already_lowered);
         }
      }
   }

   let mut lowered = HashMap::new();

   for exp in program.ast.expressions.values_mut() {
      match &mut exp.expression {
         Expression::BoundFcnLiteral(_, type_arg_nodes) => {
            for n in type_arg_nodes.iter_mut() {
               lower_type(
                  &mut n.e_type,
                  &mut program.user_defined_types,
                  &program.templated_types,
                  target,
                  &mut lowered,
               );
            }
         }
         Expression::Cast { target_type, .. } => {
            lower_type(
               target_type,
               &mut program.user_defined_types,
               &program.templated_types,
               target,
               &mut lowered,
            );
         }
         _ => (),
      }
   }

   for exp_type in program
      .ast
      .expressions
      .iter_mut()
      .map(|x| x.1.exp_type.as_mut().unwrap())
   {
      lower_type(
         exp_type,
         &mut program.user_defined_types,
         &program.templated_types,
         target,
         &mut lowered,
      );
   }

   let struct_ids: Vec<StructId> = program
      .user_defined_types
      .struct_info
      .iter()
      .filter(|x| x.1.size.is_some())
      .map(|x| x.0)
      .collect();
   for struct_id in struct_ids {
      // Taking field_types temporarily is fine, since lower_type should only ready field_types from
      // template structs (i.e. size is_none)
      let mut fts = std::mem::take(&mut program.user_defined_types.struct_info[struct_id].field_types);
      for field_type in fts.values_mut() {
         lower_type(
            &mut field_type.e_type,
            &mut program.user_defined_types,
            &program.templated_types,
            target,
            &mut lowered,
         );
      }
      program.user_defined_types.struct_info[struct_id].field_types = fts;
   }

   let union_ids: Vec<UnionId> = program
      .user_defined_types
      .union_info
      .iter()
      .filter(|x| x.1.size.is_some())
      .map(|x| x.0)
      .collect();
   for union_id in union_ids {
      // Taking field_types temporarily is fine, since lower_type should only ready field_types from
      // template unions (i.e. size is_none)
      let mut fts = std::mem::take(&mut program.user_defined_types.union_info[union_id].field_types);
      for field_type in fts.values_mut() {
         lower_type(
            &mut field_type.e_type,
            &mut program.user_defined_types,
            &program.templated_types,
            target,
            &mut lowered,
         );
      }
      program.user_defined_types.union_info[union_id].field_types = fts;
   }

   for procedure in program.procedures.values_mut() {
      lower_type(
         &mut procedure.definition.ret_type.e_type,
         &mut program.user_defined_types,
         &program.templated_types,
         target,
         &mut lowered,
      );
      for param in procedure.definition.parameters.iter_mut() {
         lower_type(
            &mut param.p_type.e_type,
            &mut program.user_defined_types,
            &program.templated_types,
            target,
            &mut lowered,
         );
      }
   }

   for body in program.procedure_bodies.values_mut() {
      for var_type in body.locals.values_mut() {
         lower_type(
            var_type,
            &mut program.user_defined_types,
            &program.templated_types,
            target,
            &mut lowered,
         );
      }
   }

   for a_global in program.non_stack_var_info.iter_mut() {
      lower_type(
         &mut a_global.1.expr_type.e_type,
         &mut program.user_defined_types,
         &program.templated_types,
         target,
         &mut lowered,
      );
   }

   program.templated_types.clear();
   program.user_defined_types.struct_info.retain(|_, v| v.size.is_some());
   program.user_defined_types.union_info.retain(|_, v| v.size.is_some());
}
