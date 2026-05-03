use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::interner::StrId;
use crate::parse::{
   Expression, ProcedureBody, ProcedureId, ProcedureNode, StructId, UnionId, UserDefinedTypeId, UserDefinedTypeInfo,
   all_expression_pools_mut,
};
use crate::semantic_analysis::validator::map_generic_to_concrete;
use crate::semantic_analysis::{StructInfo, UnionInfo};
use crate::size_info::{calculate_struct_size_info, calculate_union_size_info};
use crate::source_info::SourceInfo;
use crate::type_data::ExpressionType;
use crate::{BaseTarget, Program};

pub const DEPTH_LIMIT: u64 = 100;

pub struct SpecializationRequest {
   pub proc_and_type_arguments: (ProcedureId, Box<[ExpressionType]>),
   pub callsite: (Option<ProcedureId>, SourceInfo),
}

pub fn monomorphize(
   program: &mut Program,
   specialized_procedures: &mut IndexMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId>,
   specializations_to_create: Vec<SpecializationRequest>,
) {
   for new_spec in specializations_to_create {
      if let Some(existing_spec) = specialized_procedures.get_mut(&new_spec.proc_and_type_arguments) {
         program.procedures[*existing_spec]
            .where_instantiated
            .push(new_spec.callsite);
         continue;
      }

      let template_procedure = &program.procedures[new_spec.proc_and_type_arguments.0];

      // It would be great to do this check before we push it onto the worklist, since at the moment
      // that involves cloning a bunch of types
      let Some(body) = program.procedure_bodies.get(new_spec.proc_and_type_arguments.0) else {
         continue;
      };

      let mut cloned_procedure = clone_procedure(
         template_procedure,
         body,
         &new_spec.proc_and_type_arguments.1,
         &template_procedure.type_parameters,
      );
      cloned_procedure.0.where_instantiated.push(new_spec.callsite);

      let new_proc_id = program.procedures.insert(cloned_procedure.0);
      program.procedure_bodies.insert(new_proc_id, cloned_procedure.1);

      specialized_procedures.insert(new_spec.proc_and_type_arguments, new_proc_id);
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
            *generic_args = Box::new([]);
         }
      }
   }
   for body in program.procedure_bodies.values_mut() {
      for var_type in body.locals.values_mut() {
         lower_type(var_type, specialized_procedures);
      }
   }
   for ast in all_expression_pools_mut(&mut program.global_exprs, &mut program.procedure_bodies) {
      for expr in ast.values_mut() {
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
               .collect::<Box<_>>();

            if let Some(new_id) = specialized_procedures.get(&(*id, gargs)).copied() {
               *id = new_id;
               *generic_args = Box::new([]);
            }
         }
      }
   }
}

fn clone_procedure(
   template_procedure: &ProcedureNode,
   template_body: &ProcedureBody,
   concrete_types: &[ExpressionType],
   type_parameters: &IndexMap<StrId, IndexSet<StrId>>,
) -> (ProcedureNode, ProcedureBody) {
   let mut cloned_proc = template_procedure.clone();

   for param in cloned_proc.definition.parameters.iter_mut() {
      map_generic_to_concrete(&mut param.p_type.e_type, concrete_types, type_parameters);
   }
   map_generic_to_concrete(
      &mut cloned_proc.definition.ret_type.e_type,
      concrete_types,
      type_parameters,
   );

   cloned_proc.definition.type_parameters.clear();
   cloned_proc.type_parameters.clear();

   cloned_proc.specialized_type_parameters = type_parameters
      .keys()
      .copied()
      .zip(concrete_types.iter().cloned())
      .collect();

   (cloned_proc, template_body.clone())
}

pub fn monomorphize_types(program: &mut Program, target: BaseTarget) {
   fn lower_type(
      e: &mut ExpressionType,
      udt: &mut UserDefinedTypeInfo,
      tt: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
      target: BaseTarget,
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
         ExpressionType::ProcedurePointer {
            parameters,
            ret_type,
            variadic: _,
         } => {
            for p in parameters.iter_mut() {
               lower_type(p, udt, tt, target, already_lowered);
            }
            lower_type(ret_type, udt, tt, target, already_lowered);
         }
      }
   }

   let mut lowered = HashMap::new();

   for ast in all_expression_pools_mut(&mut program.global_exprs, &mut program.procedure_bodies) {
      for exp in ast.values_mut() {
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

         lower_type(
            exp.exp_type.as_mut().unwrap(),
            &mut program.user_defined_types,
            &program.templated_types,
            target,
            &mut lowered,
         );
      }
   }

   let struct_ids: Vec<StructId> = program
      .user_defined_types
      .struct_info
      .iter()
      .filter(|x| x.1.size.is_some())
      .map(|x| x.0)
      .collect();
   for struct_id in struct_ids {
      // Taking field_types temporarily is fine, since lower_type should only read field_types from
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
