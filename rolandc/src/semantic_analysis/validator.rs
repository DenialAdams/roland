use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::ops::Deref;

use indexmap::{IndexMap, IndexSet};
use slotmap::SlotMap;

use super::type_inference::{constraint_matches_type_or_try_constrain, lower_unknowns_in_type, try_merge_types};
use super::type_variables::{TypeConstraint, TypeVariableManager};
use super::{GlobalInfo, OwnedValidationContext, ValidationContext, VariableDetails, VariableScopeKind};
use crate::Target;
use crate::constant_folding::{self, FoldingContext};
use crate::error_handling::ErrorManager;
use crate::error_handling::error_handling_macros::{
   rolandc_error, rolandc_error_no_loc, rolandc_error_w_details, rolandc_warn,
};
use crate::interner::{Interner, StrId};
use crate::monomorphization::SpecializationRequest;
use crate::parse::{
   ArgumentNode, BinOp, BlockNode, CastType, DeclarationValue, Expression, ExpressionId, ExpressionNode,
   ExpressionPool, ExpressionTypeNode, ProcImplSource, ProcedureId, ProcedureNode, Program, Statement, StatementId,
   StrNode, UnOp, UserDefinedTypeId, UserDefinedTypeInfo, VariableId, statement_always_or_never_returns,
};
use crate::size_info::{template_type_aware_mem_alignment, template_type_aware_mem_size};
use crate::source_info::SourceInfo;
use crate::type_data::{ExpressionType, F32_TYPE, F64_TYPE, I32_TYPE, IntType, U32_TYPE, U64_TYPE, USIZE_TYPE};

pub struct SpecialProcedure {
   pub name: StrId,
   pub required: bool,
   pub input_types: Vec<ExpressionType>,
   pub return_type: ExpressionType,
}

pub fn get_special_procedures(target: Target, interner: &mut Interner) -> Box<[SpecialProcedure]> {
   match target {
      Target::Lib => Box::new([]),
      Target::Wasm4 => Box::new([
         SpecialProcedure {
            name: interner.intern("start"),
            required: false,
            input_types: vec![],
            return_type: ExpressionType::Unit,
         },
         SpecialProcedure {
            name: interner.intern("update"),
            required: true,
            input_types: vec![],
            return_type: ExpressionType::Unit,
         },
      ]),
      Target::Wasi | Target::Qbe => Box::new([SpecialProcedure {
         name: interner.intern("main"),
         required: true,
         input_types: vec![],
         return_type: ExpressionType::Unit,
      }]),
      Target::Microw8 => Box::new([
         SpecialProcedure {
            name: interner.intern("upd"),
            required: true,
            input_types: vec![],
            return_type: ExpressionType::Unit,
         },
         SpecialProcedure {
            name: interner.intern("snd"),
            required: false,
            input_types: vec![I32_TYPE],
            return_type: F32_TYPE,
         },
      ]),
   }
}

#[derive(Debug)]
enum TypeValidator {
   AnyEnum,
   Bool,
   AnyInt,
   AnySignedInt,
   AnyFloat,
   AnyPointer,
   Any,
}

fn matches(type_validation: &TypeValidator, et: &ExpressionType, validation_context: &ValidationContext) -> bool {
   let normal_matches = matches!(
      (type_validation, et),
      (TypeValidator::Any, _)
         | (TypeValidator::AnyPointer, ExpressionType::Pointer(_))
         | (TypeValidator::Bool, ExpressionType::Bool)
         | (TypeValidator::AnyInt, ExpressionType::Int(_))
         | (
            TypeValidator::AnySignedInt,
            ExpressionType::Int(IntType { signed: true, .. })
         )
         | (TypeValidator::AnyFloat, ExpressionType::Float(_))
         | (TypeValidator::AnyEnum, ExpressionType::Enum(_))
   );

   let unknown_matches = if let ExpressionType::Unknown(x) = et {
      let type_constraint = validation_context.owned.type_variables.get_data(*x).constraint;
      matches!(
         (type_validation, type_constraint),
         (TypeValidator::AnySignedInt, TypeConstraint::SignedInt)
            | (TypeValidator::AnyInt, TypeConstraint::Int | TypeConstraint::SignedInt)
            | (TypeValidator::AnyFloat, TypeConstraint::Float)
      )
   } else {
      false
   };

   normal_matches | unknown_matches
}

fn any_match(type_validations: &[TypeValidator], et: &ExpressionType, validation_context: &ValidationContext) -> bool {
   let mut any_match = false;
   for type_validation in type_validations.iter() {
      any_match |= matches(type_validation, et, validation_context);
   }
   any_match
}

pub fn str_to_builtin_type(x: &str) -> Option<ExpressionType> {
   match x {
      "bool" => Some(ExpressionType::Bool),
      "isize" => Some(crate::type_data::ISIZE_TYPE),
      "i64" => Some(crate::type_data::I64_TYPE),
      "i32" => Some(crate::type_data::I32_TYPE),
      "i16" => Some(crate::type_data::I16_TYPE),
      "i8" => Some(crate::type_data::I8_TYPE),
      "usize" => Some(crate::type_data::USIZE_TYPE),
      "u64" => Some(crate::type_data::U64_TYPE),
      "u32" => Some(crate::type_data::U32_TYPE),
      "u16" => Some(crate::type_data::U16_TYPE),
      "u8" => Some(crate::type_data::U8_TYPE),
      "f32" => Some(crate::type_data::F32_TYPE),
      "f64" => Some(crate::type_data::F64_TYPE),
      "unit" => Some(ExpressionType::Unit),
      _ => None,
   }
}

pub trait CanCheckContainsStrId {
   fn contains(&self, x: StrId) -> bool;
   fn get_index_of(&self, x: StrId) -> Option<usize>;
}

impl<V> CanCheckContainsStrId for IndexMap<StrId, V> {
   fn contains(&self, x: StrId) -> bool {
      self.contains_key(&x)
   }

   fn get_index_of(&self, x: StrId) -> Option<usize> {
      self.get_index_of(&x)
   }
}

impl CanCheckContainsStrId for IndexSet<StrId> {
   fn contains(&self, x: StrId) -> bool {
      self.contains(&x)
   }

   fn get_index_of(&self, x: StrId) -> Option<usize> {
      self.get_index_of(&x)
   }
}

impl CanCheckContainsStrId for () {
   fn contains(&self, _: StrId) -> bool {
      false
   }

   fn get_index_of(&self, _: StrId) -> Option<usize> {
      None
   }
}

pub fn resolve_type<T>(
   v_type: &mut ExpressionType,
   type_name_table: &HashMap<StrId, UserDefinedTypeId>,
   type_params: Option<&T>,
   specialized_types: Option<&HashMap<StrId, ExpressionType>>,
   err_manager: &mut ErrorManager,
   interner: &Interner,
   location_for_error: SourceInfo,
   template_types: &HashMap<UserDefinedTypeId, IndexSet<StrId>>,
) -> bool
where
   T: CanCheckContainsStrId,
{
   match v_type {
      ExpressionType::Pointer(vt) => resolve_type(
         vt,
         type_name_table,
         type_params,
         specialized_types,
         err_manager,
         interner,
         location_for_error,
         template_types,
      ),
      ExpressionType::Array(exp, _) => resolve_type(
         exp,
         type_name_table,
         type_params,
         specialized_types,
         err_manager,
         interner,
         location_for_error,
         template_types,
      ),
      ExpressionType::ProcedurePointer {
         parameters,
         ret_type: ret_val,
      } => {
         let mut resolve_result = true;
         for parameter in parameters.iter_mut() {
            resolve_result &= resolve_type(
               parameter,
               type_name_table,
               type_params,
               specialized_types,
               err_manager,
               interner,
               location_for_error,
               template_types,
            );
         }
         resolve_result &= resolve_type(
            ret_val,
            type_name_table,
            type_params,
            specialized_types,
            err_manager,
            interner,
            location_for_error,
            template_types,
         );
         resolve_result
      }
      ExpressionType::CompileError
      | ExpressionType::Enum(_)
      | ExpressionType::Never
      | ExpressionType::Unknown(_)
      | ExpressionType::Int(_)
      | ExpressionType::Float(_)
      | ExpressionType::Bool
      | ExpressionType::Unit
      | ExpressionType::Struct(_, _)
      | ExpressionType::Union(_, _)
      | ExpressionType::GenericParam(_)
      | ExpressionType::ProcedureItem(_, _) => true, // This type contains other types, but this type itself can never be written down. It should always be valid
      ExpressionType::Unresolved { name: x, generic_args } => {
         let mut args_ok = true;
         for g_arg in generic_args.iter_mut() {
            args_ok &= resolve_type(
               g_arg,
               type_name_table,
               type_params,
               specialized_types,
               err_manager,
               interner,
               location_for_error,
               template_types,
            );
         }

         let new_type = match type_name_table.get(x) {
            Some(UserDefinedTypeId::Enum(y)) => {
               if !generic_args.is_empty() {
                  rolandc_error!(
                     err_manager,
                     location_for_error,
                     "Type arguments are not supported for enum types",
                  );

                  return false;
               }
               ExpressionType::Enum(*y)
            }
            Some(UserDefinedTypeId::Union(y)) => {
               let expected_num_type_args = template_types
                  .get(&UserDefinedTypeId::Union(*y))
                  .unwrap_or(&IndexSet::new())
                  .len();
               if expected_num_type_args != generic_args.len() {
                  rolandc_error!(
                     err_manager,
                     location_for_error,
                     "Expected {} type arguments but got {}",
                     expected_num_type_args,
                     generic_args.len(),
                  );

                  return false;
               }
               ExpressionType::Union(*y, std::mem::take(generic_args))
            }
            Some(UserDefinedTypeId::Struct(y)) => {
               let expected_num_type_args = template_types
                  .get(&UserDefinedTypeId::Struct(*y))
                  .unwrap_or(&IndexSet::new())
                  .len();
               if expected_num_type_args != generic_args.len() {
                  rolandc_error!(
                     err_manager,
                     location_for_error,
                     "Expected {} type arguments but got {}",
                     expected_num_type_args,
                     generic_args.len(),
                  );

                  return false;
               }
               ExpressionType::Struct(*y, std::mem::take(generic_args))
            }
            None => {
               if let Some(bt) = str_to_builtin_type(interner.lookup(*x)) {
                  if !generic_args.is_empty() {
                     rolandc_error!(
                        err_manager,
                        location_for_error,
                        "Type arguments are not supported for builtin types",
                     );

                     return false;
                  }
                  bt
               } else if type_params.is_some_and(|tp| tp.contains(*x)) {
                  if !generic_args.is_empty() {
                     rolandc_error!(
                        err_manager,
                        location_for_error,
                        "Type arguments are not supported for type parameters",
                     );

                     return false;
                  }
                  ExpressionType::GenericParam(*x)
               } else if let Some(spec_type) = specialized_types.and_then(|st| st.get(x)) {
                  if !generic_args.is_empty() {
                     rolandc_error!(
                        err_manager,
                        location_for_error,
                        "Type arguments are not supported for type parameters",
                     );

                     return false;
                  }
                  spec_type.clone()
               } else {
                  rolandc_error!(
                     err_manager,
                     location_for_error,
                     "Undeclared type `{}`",
                     interner.lookup(*x),
                  );
                  return false;
               }
            }
         };
         *v_type = new_type;
         args_ok
      }
   }
}

pub fn validate_special_procedure_signatures(
   target: Target,
   interner: &mut Interner,
   proc_name_table: &HashMap<StrId, ProcedureId>,
   udt: &UserDefinedTypeInfo,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   err_manager: &mut ErrorManager,
) {
   let special_procs = get_special_procedures(target, interner);
   for special_proc in special_procs.iter() {
      let actual_proc = proc_name_table.get(&special_proc.name).and_then(|x| procedures.get(*x));
      if let Some(p) = actual_proc {
         if !p.named_parameters.is_empty() {
            rolandc_error!(
               err_manager,
               p.location,
               "`{}` is a special procedure for this target ({}) and is not allowed to have named parameters",
               interner.lookup(special_proc.name),
               target,
            );
         }
         if !p.definition.type_parameters.is_empty() {
            rolandc_error!(
               err_manager,
               p.location,
               "`{}` is a special procedure for this target ({}) and is not allowed to have type parameters",
               interner.lookup(special_proc.name),
               target,
            );
         }
         if !p
            .definition
            .parameters
            .iter()
            .map(|x| &x.p_type.e_type)
            .eq(special_proc.input_types.iter())
         {
            if special_proc.input_types.is_empty() {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and is not allowed to have parameters",
                  interner.lookup(special_proc.name),
                  target,
               );
            } else {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and must have the following signature: ({})",
                  interner.lookup(special_proc.name),
                  target,
                  special_proc
                     .input_types
                     .iter()
                     .map(|x| x.as_roland_type_info_like_source(interner, udt,))
                     .collect::<Vec<_>>()
                     .join(", ")
               );
            }
         }
         if p.definition.ret_type.e_type != special_proc.return_type {
            if special_proc.return_type == ExpressionType::Unit {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and must not return a value",
                  interner.lookup(special_proc.name),
                  target,
               );
            } else {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and must return {}",
                  interner.lookup(special_proc.name),
                  target,
                  special_proc.return_type.as_roland_type_info_like_source(interner, udt),
               );
            }
         }
      } else if special_proc.required {
         rolandc_error_no_loc!(
            err_manager,
            "A procedure with the name `{}` must be present for this target ({})",
            interner.lookup(special_proc.name),
            target,
         );
      }
   }
}

#[must_use]
pub fn type_and_check_validity(
   program: &mut Program,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
   owned: &mut OwnedValidationContext,
   procedures_to_check: &[ProcedureId],
) -> Vec<SpecializationRequest> {
   let mut validation_context = ValidationContext {
      owned,
      source_to_definition: &mut program.source_to_definition,
      next_var_dont_access: &mut program.next_variable,
      interner,
      ast: &mut program.ast,
      procedures: &program.procedures,
      proc_name_table: &program.procedure_name_table,
      user_defined_type_name_table: &program.user_defined_type_name_table,
      user_defined_types: &mut program.user_defined_types,
      global_info: &mut program.non_stack_var_info,
      templated_types: &program.templated_types,
   };

   for id in procedures_to_check.iter().copied() {
      let errs_before = err_manager.errors.len();
      let warnings_before = err_manager.warnings.len();

      let proc = &program.procedures[id];
      let body = &mut program.procedure_bodies[id];
      validation_context.owned.cur_procedure = Some(id);
      let num_globals = validation_context.owned.variable_types.len();

      for parameter in proc.definition.parameters.iter() {
         validation_context.owned.variable_types.insert(
            parameter.name,
            VariableDetails {
               used: false,
               declaration_location: parameter.location,
               kind: VariableScopeKind::Parameter,
               var_id: parameter.var_id,
            },
         );
         validation_context
            .owned
            .cur_procedure_locals
            .insert(parameter.var_id, parameter.p_type.e_type.clone());
      }

      type_block(err_manager, &body.block, &mut validation_context);
      fall_out_of_scope(err_manager, &mut validation_context, num_globals);

      std::mem::swap(&mut validation_context.owned.cur_procedure_locals, &mut body.locals);

      // Ensure that the last statement is a return statement
      // (it has already been type checked, so we don't have to check that)
      match (&proc.definition.ret_type.e_type, body.block.statements.last().copied()) {
         (ExpressionType::Unit, _) => (),
         (_, Some(s)) if statement_always_or_never_returns(s, validation_context.ast) => (),
         (x, _) => {
            let x_str = x.as_roland_type_info(
               validation_context.interner,
               validation_context.user_defined_types,
               validation_context.procedures,
               &validation_context.owned.type_variables,
            );
            let mut err_details = vec![(proc.location, "procedure defined")];
            if let Some(fs) = body.block.statements.last() {
               let loc = validation_context.ast.statements[*fs].location;
               err_details.push((loc, "actual final statement"));
            }
            rolandc_error_w_details!(
               err_manager,
               &err_details,
               "Procedure `{}` is declared to return type {} but is missing a final return statement",
               validation_context.interner.lookup(proc.definition.name.str),
               x_str,
            );
         }
      }

      for err in err_manager.errors[errs_before..]
         .iter_mut()
         .chain(err_manager.warnings[warnings_before..].iter_mut())
      {
         let mut this_proc = proc;
         while let Some(wa) = this_proc.where_instantiated.first().copied() {
            err.came_from_stack.push(wa.1);
            if let Some(callee_proc) = wa.0 {
               this_proc = validation_context.procedures.get(callee_proc).unwrap();
            }
         }
      }
   }
   validation_context.owned.cur_procedure = None;

   validation_context.owned.procedures_to_specialize.retain_mut(|x| {
      for et in x.proc_and_type_arguments.1.iter_mut() {
         lower_unknowns_in_type(et, &validation_context.owned.type_variables);
      }
      x.proc_and_type_arguments.1.iter().all(ExpressionType::is_concrete)
   });

   std::mem::take(&mut validation_context.owned.procedures_to_specialize)
}

fn type_statement(err_manager: &mut ErrorManager, statement: StatementId, validation_context: &mut ValidationContext) {
   let mut stmt_loc = validation_context.ast.statements[statement].location;
   let mut the_statement = std::mem::replace(
      &mut validation_context.ast.statements[statement].statement,
      Statement::Break,
   );
   type_statement_inner(err_manager, &mut the_statement, &mut stmt_loc, validation_context);
   validation_context.ast.statements[statement].statement = the_statement;
   validation_context.ast.statements[statement].location = stmt_loc;
}

fn type_statement_inner(
   err_manager: &mut ErrorManager,
   statement: &mut Statement,
   stmt_loc: &mut SourceInfo,
   validation_context: &mut ValidationContext,
) {
   match statement {
      Statement::Assignment(lhs, rhs) => {
         type_expression(err_manager, *lhs, validation_context);
         type_expression(err_manager, *rhs, validation_context);

         let merged = try_merge_types_of_two_distinct_expressions(
            *lhs,
            *rhs,
            &validation_context.ast.expressions,
            &mut validation_context.owned.type_variables,
         );

         let len = &validation_context.ast.expressions[*lhs];
         let en = &validation_context.ast.expressions[*rhs];

         let lhs_type = len.exp_type.as_ref().unwrap();
         let rhs_type = en.exp_type.as_ref().unwrap();

         if lhs_type.is_or_contains_or_points_to_error() || rhs_type.is_or_contains_or_points_to_error() {
            // avoid cascading errors
         } else if !merged && !rhs_type.is_never() {
            rolandc_error_w_details!(
               err_manager,
               &[(len.location, "left hand side"), (en.location, "right hand side")],
               "Left hand side of assignment has type {} which does not match the type of the right hand side {}",
               lhs_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               ),
               rhs_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               ),
            );
         } else if !len
            .expression
            .is_lvalue(&validation_context.ast.expressions, validation_context.global_info)
         {
            if len
               .expression
               .is_lvalue_disregard_consts(&validation_context.ast.expressions)
            {
               rolandc_error!(
                  err_manager,
                  len.location,
                  "Left hand side of assignment is a constant, which does not have a memory location and can't be reassigned"
               );
            } else {
               rolandc_error!(
                  err_manager,
                  len.location,
                  "Left hand side of assignment is not a valid memory location; i.e. a variable, field, or array index"
               );
            }
         }
      }
      Statement::Block(bn) => {
         type_block(err_manager, bn, validation_context);
      }
      Statement::Continue => {
         if validation_context.owned.loop_depth == 0 {
            rolandc_error!(err_manager, *stmt_loc, "Continue statement can only be used in a loop");
         }
      }
      Statement::Break => {
         if validation_context.owned.loop_depth == 0 {
            rolandc_error!(err_manager, *stmt_loc, "Break statement can only be used in a loop");
         }
      }
      Statement::For {
         induction_var_name: var,
         range_start: start,
         range_end: end,
         body: bn,
         range_inclusive: inclusive,
         induction_var: var_id,
      } => {
         type_expression(err_manager, *start, validation_context);
         type_expression(err_manager, *end, validation_context);

         let mut constrained_to_int = false;
         for expr_id in [*start, *end] {
            if let ExpressionType::Unknown(x) = validation_context.ast.expressions[expr_id].exp_type.as_ref().unwrap() {
               let tvd = validation_context.owned.type_variables.get_data_mut(*x);
               constrained_to_int = tvd.add_constraint(TypeConstraint::Int).is_ok();
            }
         }

         let merged = try_merge_types_of_two_distinct_expressions(
            *start,
            *end,
            &validation_context.ast.expressions,
            &mut validation_context.owned.type_variables,
         );

         let start_expr = &validation_context.ast.expressions[*start];
         let end_expr = &validation_context.ast.expressions[*end];

         let result_type = if merged
            && (constrained_to_int || matches!(start_expr.exp_type.as_ref().unwrap(), ExpressionType::Int(_)))
         {
            start_expr.exp_type.clone().unwrap()
         } else if start_expr
            .exp_type
            .as_ref()
            .unwrap()
            .is_or_contains_or_points_to_error()
            || end_expr.exp_type.as_ref().unwrap().is_or_contains_or_points_to_error()
         {
            ExpressionType::CompileError
         } else {
            rolandc_error_w_details!(
               err_manager,
               &[
                  (start_expr.location, "start of range"),
                  (end_expr.location, "end of range")
               ],
               "Start and end of range must be integer types of the same kind; got types `{}` and `{}`",
               start_expr.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               ),
               end_expr.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               ),
            );
            ExpressionType::CompileError
         };

         if *inclusive {
            rolandc_error!(err_manager, *stmt_loc, "Inclusive ranges are not currently supported.");
         }

         let vars_before = validation_context.owned.variable_types.len();
         *var_id = declare_variable(err_manager, var, validation_context);
         validation_context
            .owned
            .cur_procedure_locals
            .insert(*var_id, result_type);

         type_loop_block(err_manager, bn, validation_context);

         fall_out_of_scope(err_manager, validation_context, vars_before);
      }
      Statement::While(cond, bn) => {
         type_expression(err_manager, *cond, validation_context);

         let cond_node = &validation_context.ast.expressions[*cond];
         let is_bool = try_merge_types(
            &ExpressionType::Bool,
            cond_node.exp_type.as_ref().unwrap(),
            &mut validation_context.owned.type_variables,
         );
         let cond_type = cond_node.exp_type.as_ref().unwrap();
         if !is_bool && !cond_type.is_or_contains_or_points_to_error() {
            rolandc_error!(
               err_manager,
               cond_node.location,
               "Type of while condition must be a bool; got {}",
               cond_node.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
         }

         type_loop_block(err_manager, bn, validation_context);
      }
      Statement::Loop(bn) => {
         type_loop_block(err_manager, bn, validation_context);
      }
      Statement::Defer(si) => {
         if matches!(
            validation_context.ast.statements[*si].statement,
            Statement::VariableDeclaration { .. }
         ) {
            rolandc_error!(
               err_manager,
               validation_context.ast.statements[*si].location,
               "Deferring a variable declaration at top level is not allowed"
            );
         } else {
            type_statement(err_manager, *si, validation_context);
         }
      }
      Statement::Expression(en) => {
         type_expression(err_manager, *en, validation_context);
      }
      Statement::IfElse {
         cond,
         then,
         otherwise,
         constant: true,
      } => {
         type_expression(err_manager, *cond, validation_context);
         let en = &validation_context.ast.expressions[*cond];
         let if_exp_type = en.exp_type.as_ref().unwrap();
         let is_bool = try_merge_types(
            &ExpressionType::Bool,
            if_exp_type,
            &mut validation_context.owned.type_variables,
         );
         if if_exp_type.is_or_contains_or_points_to_error() {
            return;
         }
         if !is_bool {
            rolandc_error!(
               err_manager,
               en.location,
               "Type of when condition must be a bool; got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
            return;
         }
         fold_expr_id(*cond, err_manager, validation_context);
         let en = &mut validation_context.ast.expressions[*cond];
         match en.expression {
            Expression::BoolLiteral(true) => {
               type_block(err_manager, then, validation_context);
               *stmt_loc = then.location;
               let if_blk = std::mem::replace(
                  then,
                  BlockNode {
                     statements: Vec::new(),
                     location: *stmt_loc,
                  },
               );
               *statement = Statement::Block(if_blk);
            }
            Expression::BoolLiteral(false) => {
               type_statement(err_manager, *otherwise, validation_context);
               *stmt_loc = validation_context.ast.statements[*otherwise].location;
               let else_stmt = std::mem::replace(
                  &mut validation_context.ast.statements[*otherwise].statement,
                  Statement::Break,
               );
               *statement = else_stmt;
            }
            _ => {
               rolandc_error!(
                  err_manager,
                  en.location,
                  "Value of when condition can't be constant folded",
               );
            }
         }
      }
      Statement::IfElse {
         cond: en,
         then: block_1,
         otherwise: block_2,
         constant: false,
      } => {
         type_block(err_manager, block_1, validation_context);
         type_statement(err_manager, *block_2, validation_context);
         type_expression(err_manager, *en, validation_context);

         let en = &validation_context.ast.expressions[*en];
         let if_exp_type = en.exp_type.as_ref().unwrap();
         let is_bool = try_merge_types(
            &ExpressionType::Bool,
            if_exp_type,
            &mut validation_context.owned.type_variables,
         );
         if !is_bool && !if_exp_type.is_or_contains_or_points_to_error() {
            rolandc_error!(
               err_manager,
               en.location,
               "Type of if condition must be a bool; got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
         }
      }
      Statement::Return(en) => {
         type_expression(err_manager, *en, validation_context);
         let cur_procedure_ret = &validation_context.procedures[validation_context.owned.cur_procedure.unwrap()]
            .definition
            .ret_type
            .e_type;

         let return_type_matches = try_merge_types(
            cur_procedure_ret,
            validation_context.ast.expressions[*en].exp_type.as_ref().unwrap(),
            &mut validation_context.owned.type_variables,
         );

         let en = &validation_context.ast.expressions[*en];

         if !en.exp_type.as_ref().unwrap().is_or_contains_or_points_to_error()
            && !en.exp_type.as_ref().unwrap().is_never()
            && !return_type_matches
         {
            rolandc_error!(
               err_manager,
               en.location,
               "Value of return statement must match declared return type {}; got {}",
               cur_procedure_ret.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               ),
               en.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
         }
      }
      Statement::VariableDeclaration {
         var_name: id,
         value: opt_enid,
         declared_type: dt,
         var_id,
         storage,
      } => {
         if let DeclarationValue::Expr(enid) = opt_enid {
            type_expression(err_manager, *enid, validation_context);
         }

         let result_type_node = match dt {
            Some(v) => {
               let spec_params = validation_context
                  .owned
                  .cur_procedure
                  .map(|x| &validation_context.procedures[x].specialized_type_parameters);
               if resolve_type::<()>(
                  &mut v.e_type,
                  validation_context.user_defined_type_name_table,
                  None,
                  spec_params,
                  err_manager,
                  validation_context.interner,
                  v.location,
                  validation_context.templated_types,
               ) {
                  if let DeclarationValue::Expr(enid) = opt_enid {
                     let merged = try_merge_types(
                        &v.e_type,
                        validation_context.ast.expressions[*enid].exp_type.as_ref().unwrap(),
                        &mut validation_context.owned.type_variables,
                     );
                     if !merged {
                        error_type_declared_vs_actual(
                           v,
                           &validation_context.ast.expressions[*enid],
                           validation_context.interner,
                           validation_context.user_defined_types,
                           validation_context.procedures,
                           &validation_context.owned.type_variables,
                           err_manager,
                        );
                     }
                  }
                  v.clone()
               } else {
                  ExpressionTypeNode {
                     e_type: ExpressionType::CompileError,
                     location: dt.as_ref().unwrap().location,
                  }
               }
            }
            None => {
               if let DeclarationValue::Expr(en) = opt_enid {
                  ExpressionTypeNode {
                     e_type: validation_context.ast.expressions[*en].exp_type.clone().unwrap(),
                     location: validation_context.ast.expressions[*en].location,
                  }
               } else {
                  rolandc_error!(
                     err_manager,
                     id.location,
                     "Uninitialized variables must be declared with a type",
                  );
                  ExpressionTypeNode {
                     e_type: ExpressionType::CompileError,
                     location: *stmt_loc,
                  }
               }
            }
         };

         *var_id = declare_variable(err_manager, id, validation_context);

         if let Some(storage_kind) = storage {
            validation_context.global_info.insert(
               *var_id,
               GlobalInfo {
                  expr_type: result_type_node,
                  initializer: match opt_enid {
                     DeclarationValue::Expr(expression_id) => Some(*expression_id),
                     DeclarationValue::Uninit | DeclarationValue::None => None,
                  },
                  location: *stmt_loc,
                  kind: *storage_kind,
                  name: id.str,
               },
            );
         } else {
            validation_context
               .owned
               .cur_procedure_locals
               .insert(*var_id, result_type_node.e_type);
         }
      }
   }
}

#[must_use]
fn declare_variable(
   err_manager: &mut ErrorManager,
   id: &StrNode,
   validation_context: &mut ValidationContext,
) -> VariableId {
   let next_var = validation_context.next_var();
   if validation_context.owned.variable_types.contains_key(&id.str) {
      rolandc_error!(
         err_manager,
         id.location,
         "Variable shadowing is not supported at this time (`{}`)",
         validation_context.interner.lookup(id.str)
      );
   }
   validation_context.owned.variable_types.insert(
      id.str,
      VariableDetails {
         declaration_location: id.location,
         used: false,
         kind: VariableScopeKind::Local,
         var_id: next_var,
      },
   );
   next_var
}

fn fall_out_of_scope(
   err_manager: &mut ErrorManager,
   validation_context: &mut ValidationContext,
   first_var_in_scope: usize,
) {
   for (k, v) in validation_context.owned.variable_types.drain(first_var_in_scope..) {
      if !v.used {
         let begin = match v.kind {
            VariableScopeKind::Parameter => "Parameter",
            VariableScopeKind::Local => "Local variable",
            VariableScopeKind::Global => "Global variable",
         };
         rolandc_warn!(
            err_manager,
            v.declaration_location,
            "{} `{}` is unused",
            begin,
            validation_context.interner.lookup(k),
         );
      }
   }
}

fn type_loop_block(err_manager: &mut ErrorManager, bn: &BlockNode, validation_context: &mut ValidationContext) {
   validation_context.owned.loop_depth += 1;
   type_block(err_manager, bn, validation_context);
   validation_context.owned.loop_depth -= 1;
}

fn type_block(err_manager: &mut ErrorManager, bn: &BlockNode, validation_context: &mut ValidationContext) {
   let num_vars = validation_context.owned.variable_types.len();

   for statement in bn.statements.iter().copied() {
      type_statement(err_manager, statement, validation_context);
   }

   fall_out_of_scope(err_manager, validation_context, num_vars);
}

fn type_expression(
   err_manager: &mut ErrorManager,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
) {
   let expr_location = validation_context.ast.expressions[expr_index].location;

   // Resolve types and names first
   match &mut validation_context.ast.expressions[expr_index].expression {
      Expression::Cast { target_type, .. } => {
         let spec_params = validation_context
            .owned
            .cur_procedure
            .map(|x| &validation_context.procedures[x].specialized_type_parameters);
         if !resolve_type::<()>(
            target_type,
            validation_context.user_defined_type_name_table,
            None,
            spec_params,
            err_manager,
            validation_context.interner,
            expr_location,
            validation_context.templated_types,
         ) {
            *target_type = ExpressionType::CompileError;
         }
      }
      Expression::UnresolvedVariable(id) => match validation_context.owned.variable_types.get_mut(&id.str) {
         Some(var_info) => {
            var_info.used = true;
            validation_context
               .source_to_definition
               .insert(expr_location, var_info.declaration_location);
            validation_context.ast.expressions[expr_index].expression = Expression::Variable(var_info.var_id);
         }
         None => {
            if let Some(proc_id) = validation_context.proc_name_table.get(&id.str).copied() {
               validation_context
                  .source_to_definition
                  .insert(id.location, validation_context.procedures[proc_id].location);
               validation_context.ast.expressions[expr_index].expression =
                  Expression::BoundFcnLiteral(proc_id, Box::new([]));
            }
         }
      },
      Expression::UnresolvedProcLiteral(name, g_args) => {
         let spec_params = validation_context
            .owned
            .cur_procedure
            .map(|x| &validation_context.procedures[x].specialized_type_parameters);
         for g_arg in g_args.iter_mut() {
            resolve_type::<()>(
               &mut g_arg.e_type,
               validation_context.user_defined_type_name_table,
               None,
               spec_params,
               err_manager,
               validation_context.interner,
               g_arg.location,
               validation_context.templated_types,
            );
         }

         if let Some(proc_id) = validation_context.proc_name_table.get(&name.str).copied() {
            validation_context
               .source_to_definition
               .insert(name.location, validation_context.procedures[proc_id].location);
            validation_context.ast.expressions[expr_index].expression =
               Expression::BoundFcnLiteral(proc_id, std::mem::take(g_args));
         }
      }
      Expression::UnresolvedStructLiteral(base_type_node, _, _) => {
         let spec_params = validation_context
            .owned
            .cur_procedure
            .map(|x| &validation_context.procedures[x].specialized_type_parameters);
         if let ExpressionType::Unresolved { name, generic_args } = &mut base_type_node.e_type
            && generic_args.is_empty()
            && let Some(UserDefinedTypeId::Struct(s_id)) =
               validation_context.user_defined_type_name_table.get(name).copied()
         {
            let expected_num_type_args = validation_context
               .templated_types
               .get(&UserDefinedTypeId::Struct(s_id))
               .unwrap_or(&IndexSet::new())
               .len();
            if expected_num_type_args > 0 {
               *generic_args = (0..expected_num_type_args)
                  .map(|_| {
                     ExpressionType::Unknown(
                        validation_context
                           .owned
                           .type_variables
                           .new_type_variable(TypeConstraint::None),
                     )
                  })
                  .collect();
            }
         }
         if !resolve_type::<()>(
            &mut base_type_node.e_type,
            validation_context.user_defined_type_name_table,
            None,
            spec_params,
            err_manager,
            validation_context.interner,
            base_type_node.location,
            validation_context.templated_types,
         ) {
            base_type_node.e_type = ExpressionType::CompileError;
         }
      }
      _ => (),
   }

   let mut the_expr = std::mem::replace(
      &mut validation_context.ast.expressions[expr_index].expression,
      Expression::UnitLiteral,
   );
   validation_context.ast.expressions[expr_index].exp_type =
      Some(get_type(&mut the_expr, expr_location, err_manager, validation_context));
   validation_context.ast.expressions[expr_index].expression = the_expr;
}

fn get_type(
   expr: &mut Expression,
   expr_location: SourceInfo,
   err_manager: &mut ErrorManager,
   validation_context: &mut ValidationContext,
) -> ExpressionType {
   match expr {
      Expression::UnitLiteral => ExpressionType::Unit,
      Expression::BoolLiteral(_) => ExpressionType::Bool,
      Expression::IntLiteral { .. } => {
         let new_type_variable = validation_context
            .owned
            .type_variables
            .new_type_variable(TypeConstraint::Int);
         ExpressionType::Unknown(new_type_variable)
      }
      Expression::FloatLiteral(_) => {
         let new_type_variable = validation_context
            .owned
            .type_variables
            .new_type_variable(TypeConstraint::Float);
         ExpressionType::Unknown(new_type_variable)
      }
      Expression::StringLiteral(_) => ExpressionType::Struct(validation_context.owned.string_struct_id, Box::new([])),
      Expression::Cast {
         cast_type,
         target_type,
         expr: expr_id,
      } => {
         type_expression(err_manager, *expr_id, validation_context);

         if target_type.is_or_contains_or_points_to_error() {
            // this can occur when the target type is unresolved
            // not only does this hide extraneous error messages from the user, this also prevents panicking when
            // we check the size of an error type
            return ExpressionType::CompileError;
         }

         let from_type_is_unknown_int = {
            let exp_type = validation_context.ast.expressions[*expr_id].exp_type.as_ref().unwrap();
            match exp_type {
               ExpressionType::Unknown(v) => {
                  matches!(
                     validation_context.owned.type_variables.get_data(*v).constraint,
                     TypeConstraint::Int
                  )
               }
               _ => false,
            }
         };

         let from_int_literal = matches!(
            validation_context.ast.expressions[*expr_id].expression,
            Expression::IntLiteral {
               val: _,
               synthetic: false
            }
         );

         if from_int_literal && from_type_is_unknown_int && *cast_type == CastType::Transmute {
            'b: {
               let guessed_source_type = if target_type.is_pointer() {
                  &USIZE_TYPE
               } else if matches!(*target_type, F64_TYPE) {
                  &U64_TYPE
               } else if matches!(*target_type, F32_TYPE) {
                  &U32_TYPE
               } else if matches!(target_type, ExpressionType::Enum(_)) {
                  match target_type {
                     ExpressionType::Enum(x) => {
                        &validation_context
                           .user_defined_types
                           .enum_info
                           .get(*x)
                           .unwrap()
                           .base_type
                     }
                     _ => unreachable!(),
                  }
               } else {
                  break 'b;
               };
               try_merge_types(
                  guessed_source_type,
                  validation_context.ast.expressions[*expr_id].exp_type.as_ref().unwrap(),
                  &mut validation_context.owned.type_variables,
               );
            }
         }

         lower_unknowns_in_type(
            validation_context.ast.expressions[*expr_id].exp_type.as_mut().unwrap(),
            &validation_context.owned.type_variables,
         );

         let e = &validation_context.ast.expressions[*expr_id];
         let e_type = e.exp_type.as_ref().unwrap();

         if e_type.is_or_contains_or_points_to_error() {
            // Avoid cascading errors
            return ExpressionType::CompileError;
         }

         match cast_type {
            CastType::As => {
               let valid_cast = match target_type {
                  ExpressionType::Int(_) => any_match(
                     &[TypeValidator::AnyFloat, TypeValidator::AnyInt, TypeValidator::Bool],
                     e_type,
                     validation_context,
                  ),
                  ExpressionType::Float(_) => any_match(
                     &[TypeValidator::AnyFloat, TypeValidator::AnyInt],
                     e_type,
                     validation_context,
                  ),
                  _ => false,
               };

               if valid_cast {
                  target_type.clone()
               } else {
                  rolandc_error_w_details!(
                     err_manager,
                     &[(expr_location, "as"), (e.location, "operand")],
                     "As encountered an operand of type {} which can not be cast to type {}",
                     e_type.as_roland_type_info(
                        validation_context.interner,
                        validation_context.user_defined_types,
                        validation_context.procedures,
                        &validation_context.owned.type_variables
                     ),
                     target_type.as_roland_type_info(
                        validation_context.interner,
                        validation_context.user_defined_types,
                        validation_context.procedures,
                        &validation_context.owned.type_variables
                     ),
                  );
                  ExpressionType::CompileError
               }
            }
            CastType::Transmute => {
               if e_type.size_is_unknown() {
                  rolandc_error!(
                     err_manager,
                     e.location,
                     "Transmute encountered an operand whose size is not yet known",
                  );
                  return ExpressionType::CompileError;
               }

               let size_source = template_type_aware_mem_size(
                  e_type,
                  validation_context.user_defined_types,
                  validation_context.owned.target,
                  validation_context.templated_types,
               );
               let size_target = template_type_aware_mem_size(
                  target_type,
                  validation_context.user_defined_types,
                  validation_context.owned.target,
                  validation_context.templated_types,
               );

               if size_source == size_target {
                  #[derive(PartialEq)]
                  enum AlignOrUnknown {
                     Alignment(u32),
                     Unknown,
                  }
                  impl Display for AlignOrUnknown {
                     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        match self {
                           AlignOrUnknown::Alignment(x) => x.fmt(f),
                           AlignOrUnknown::Unknown => f.write_str("?"),
                        }
                     }
                  }
                  impl PartialOrd for AlignOrUnknown {
                     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                        match (self, other) {
                           (AlignOrUnknown::Alignment(x), AlignOrUnknown::Alignment(y)) => x.partial_cmp(y),
                           _ => None,
                        }
                     }
                  }
                  let (alignment_source, alignment_target) = {
                     fn get_align_or_unknown(a_type: &ExpressionType, ctx: &ValidationContext) -> AlignOrUnknown {
                        if a_type.size_is_unknown() {
                           return AlignOrUnknown::Unknown;
                        }
                        AlignOrUnknown::Alignment(template_type_aware_mem_alignment(
                           a_type,
                           ctx.user_defined_types,
                           ctx.owned.target,
                           ctx.templated_types,
                        ))
                     }

                     let source_base_type = e_type.get_type_or_type_being_pointed_to();
                     let target_base_type = target_type.get_type_or_type_being_pointed_to();

                     (
                        get_align_or_unknown(source_base_type, validation_context),
                        get_align_or_unknown(target_base_type, validation_context),
                     )
                  };

                  let alignment_cmp_not_good = e_type.is_pointer()
                     && target_type.is_pointer()
                     && alignment_target != AlignOrUnknown::Alignment(1)
                     && (alignment_source < alignment_target);

                  let e_is_pointer_to_unit =
                     e_type.is_pointer() && *e_type.get_type_or_type_being_pointed_to() == ExpressionType::Unit;

                  if alignment_cmp_not_good && !e_is_pointer_to_unit {
                     rolandc_error!(
                        err_manager,
                        e.location,
                        "Transmute encountered an operand of type {}, which can't be transmuted to type {} as the alignment requirements would not be met ({} vs {})",
                        e_type.as_roland_type_info(
                           validation_context.interner,
                           validation_context.user_defined_types,
                           validation_context.procedures,
                           &validation_context.owned.type_variables
                        ),
                        target_type.as_roland_type_info(
                           validation_context.interner,
                           validation_context.user_defined_types,
                           validation_context.procedures,
                           &validation_context.owned.type_variables
                        ),
                        alignment_source,
                        alignment_target,
                     );
                     ExpressionType::CompileError
                  } else {
                     target_type.clone()
                  }
               } else {
                  rolandc_error!(
                     err_manager,
                     e.location,
                     "Transmute encountered an operand of type {} which can't be transmuted to type {} as the sizes do not match ({} vs {})",
                     e_type.as_roland_type_info(
                        validation_context.interner,
                        validation_context.user_defined_types,
                        validation_context.procedures,
                        &validation_context.owned.type_variables
                     ),
                     target_type.as_roland_type_info(
                        validation_context.interner,
                        validation_context.user_defined_types,
                        validation_context.procedures,
                        &validation_context.owned.type_variables
                     ),
                     size_source,
                     size_target,
                  );
                  ExpressionType::CompileError
               }
            }
         }
      }
      Expression::BinaryOperator { operator, lhs, rhs } => {
         type_expression(err_manager, *lhs, validation_context);
         type_expression(err_manager, *rhs, validation_context);

         let correct_arg_types: &[TypeValidator] = match operator {
            BinOp::Add
            | BinOp::Subtract
            | BinOp::Multiply
            | BinOp::Divide
            | BinOp::GreaterThan
            | BinOp::GreaterThanOrEqualTo
            | BinOp::LessThan
            | BinOp::LessThanOrEqualTo => &[TypeValidator::AnyInt, TypeValidator::AnyFloat],
            BinOp::LogicalAnd | BinOp::LogicalOr => &[TypeValidator::Bool],
            BinOp::Equality | BinOp::NotEquality => &[
               TypeValidator::AnyInt,
               TypeValidator::Bool,
               TypeValidator::AnyEnum,
               TypeValidator::AnyFloat,
               TypeValidator::AnyPointer,
            ],
            BinOp::BitwiseAnd | BinOp::BitwiseOr | BinOp::BitwiseXor => &[TypeValidator::AnyInt, TypeValidator::Bool],
            BinOp::BitwiseLeftShift | BinOp::BitwiseRightShift | BinOp::Remainder => &[TypeValidator::AnyInt],
         };

         let merged = try_merge_types_of_two_distinct_expressions(
            *lhs,
            *rhs,
            &validation_context.ast.expressions,
            &mut validation_context.owned.type_variables,
         );

         lower_unknowns_in_type(
            validation_context.ast.expressions[*lhs].exp_type.as_mut().unwrap(),
            &validation_context.owned.type_variables,
         );
         lower_unknowns_in_type(
            validation_context.ast.expressions[*rhs].exp_type.as_mut().unwrap(),
            &validation_context.owned.type_variables,
         );

         let lhs_expr = &validation_context.ast.expressions[*lhs];
         let rhs_expr = &validation_context.ast.expressions[*rhs];

         let lhs_type = lhs_expr.exp_type.as_ref().unwrap();
         let rhs_type = rhs_expr.exp_type.as_ref().unwrap();

         if lhs_type.is_or_contains_or_points_to_error() || rhs_type.is_or_contains_or_points_to_error() {
            // Avoid cascading errors
            ExpressionType::CompileError
         } else if !any_match(correct_arg_types, lhs_type, validation_context) {
            rolandc_error!(
               err_manager,
               lhs_expr.location,
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {}",
               operator,
               correct_arg_types,
               lhs_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
            ExpressionType::CompileError
         } else if !any_match(correct_arg_types, rhs_type, validation_context) {
            rolandc_error!(
               err_manager,
               rhs_expr.location,
               "Binary operator {:?} requires RHS to have type matching {:?}; instead got {}",
               operator,
               correct_arg_types,
               rhs_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
            ExpressionType::CompileError
         } else if !merged {
            rolandc_error_w_details!(
               err_manager,
               &[
                  (lhs_expr.location, "left hand side"),
                  (rhs_expr.location, "right hand side")
               ],
               "Binary operator {:?} requires LHS and RHS to have identical types; instead got {} and {}",
               operator,
               lhs_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               ),
               rhs_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
            ExpressionType::CompileError
         } else {
            match operator {
               BinOp::Add
               | BinOp::Subtract
               | BinOp::Multiply
               | BinOp::Divide
               | BinOp::Remainder
               | BinOp::BitwiseAnd
               | BinOp::BitwiseOr
               | BinOp::BitwiseXor
               | BinOp::BitwiseLeftShift
               | BinOp::BitwiseRightShift => lhs_type.clone(),
               BinOp::Equality
               | BinOp::NotEquality
               | BinOp::GreaterThan
               | BinOp::GreaterThanOrEqualTo
               | BinOp::LessThan
               | BinOp::LessThanOrEqualTo
               | BinOp::LogicalAnd
               | BinOp::LogicalOr => ExpressionType::Bool,
            }
         }
      }
      Expression::UnaryOperator(un_op, e) => {
         type_expression(err_manager, *e, validation_context);
         lower_unknowns_in_type(
            validation_context.ast.expressions[*e].exp_type.as_mut().unwrap(),
            &validation_context.owned.type_variables,
         );

         let e = &validation_context.ast.expressions[*e];

         if *un_op == UnOp::AddressOf
            && let ExpressionType::ProcedureItem(proc_id, bound_type_params) = e.exp_type.as_ref().unwrap()
         {
            // special case
            *un_op = UnOp::TakeProcedurePointer;

            let proc = &validation_context.procedures[*proc_id];

            if proc.impl_source == ProcImplSource::Builtin {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Procedure pointers can't be taken to compiler builtins"
               );
               return ExpressionType::CompileError;
            }

            if !proc.named_parameters.is_empty() {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Procedure pointers can't be taken to procedures with named arguments"
               );
               return ExpressionType::CompileError;
            }

            let mut parameters: Box<[ExpressionType]> = proc
               .definition
               .parameters
               .iter()
               .map(|x| x.p_type.e_type.clone())
               .collect();

            for param in parameters.iter_mut() {
               map_generic_to_concrete(param, bound_type_params, &proc.type_parameters);
            }

            let mut ret_type = proc.definition.ret_type.e_type.clone();
            map_generic_to_concrete(&mut ret_type, bound_type_params, &proc.type_parameters);

            return ExpressionType::ProcedurePointer {
               parameters,
               ret_type: Box::new(ret_type),
            };
         }

         if *un_op == UnOp::Negate
            && let ExpressionType::Unknown(x) = e.exp_type.as_ref().unwrap()
         {
            let tvd = validation_context.owned.type_variables.get_data_mut(*x);
            if tvd.constraint == TypeConstraint::Int {
               // could be a float, or totally unknown
               tvd.add_constraint(TypeConstraint::SignedInt).unwrap();
            }
         }

         let (correct_type, node_type): (&[TypeValidator], _) = match un_op {
            UnOp::Dereference => {
               let new_type = match e.exp_type.as_ref().unwrap() {
                  ExpressionType::Pointer(inner) => inner.deref().clone(),
                  _ => {
                     // No message; let the type matcher throw the error
                     ExpressionType::CompileError
                  }
               };
               (&[TypeValidator::AnyPointer], new_type)
            }
            UnOp::Negate => (
               &[TypeValidator::AnySignedInt, TypeValidator::AnyFloat],
               e.exp_type.clone().unwrap(),
            ),
            UnOp::Complement => (
               &[TypeValidator::Bool, TypeValidator::AnyInt],
               e.exp_type.clone().unwrap(),
            ),
            UnOp::AddressOf => {
               let new_type = ExpressionType::Pointer(Box::new(e.exp_type.clone().unwrap()));
               (&[TypeValidator::Any], new_type)
            }
            // There is no syntactic construct for this -
            // already handled as a special case for & above
            UnOp::TakeProcedurePointer => unreachable!(),
         };

         if e.exp_type.as_ref().unwrap().is_or_contains_or_points_to_error() {
            // Avoid cascading errors
            ExpressionType::CompileError
         } else if !any_match(correct_type, e.exp_type.as_ref().unwrap(), validation_context) {
            rolandc_error!(
               err_manager,
               e.location,
               "Expected type {:?} for expression {:?}; instead got {}",
               correct_type,
               un_op,
               e.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
            ExpressionType::CompileError
         } else {
            node_type
         }
      }
      Expression::BoundFcnLiteral(id, type_arguments) => {
         let proc = validation_context.procedures.get(*id).unwrap();

         if type_arguments.is_empty() && !proc.type_parameters.is_empty() {
            *type_arguments = ((0..proc.type_parameters.len()).map(|_| ExpressionTypeNode {
               e_type: ExpressionType::Unknown(
                  validation_context
                     .owned
                     .type_variables
                     .new_type_variable(TypeConstraint::None),
               ),
               location: expr_location,
            }))
            .collect();
         }

         let check_result = check_procedure_item(
            *id,
            proc.definition.name.str,
            &proc.type_parameters,
            expr_location,
            type_arguments,
            validation_context.interner,
            validation_context.user_defined_types,
            validation_context.procedures,
            err_manager,
            &mut validation_context.owned.type_variables,
         );

         if check_result.1 && !type_arguments.is_empty() {
            validation_context
               .owned
               .procedures_to_specialize
               .push(SpecializationRequest {
                  proc_and_type_arguments: (
                     *id,
                     type_arguments
                        .iter()
                        .map(|x| x.e_type.clone())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                  ),
                  callsite: (validation_context.owned.cur_procedure, expr_location),
               });
         }

         check_result.0
      }
      Expression::UnresolvedProcLiteral(name, _) => {
         rolandc_error!(
            err_manager,
            name.location,
            "Encountered undefined symbol `{}`",
            validation_context.interner.lookup(name.str)
         );
         ExpressionType::CompileError
      }
      Expression::UnresolvedVariable(id) => {
         rolandc_error!(
            err_manager,
            expr_location,
            "Encountered undefined symbol `{}`",
            validation_context.interner.lookup(id.str)
         );
         ExpressionType::CompileError
      }
      Expression::UnresolvedStructLiteral(provided_type, fields, base_ident_location) => {
         for field_val in fields.iter().filter_map(|x| x.1) {
            type_expression(err_manager, field_val, validation_context);
         }

         let final_type = std::mem::replace(&mut provided_type.e_type, ExpressionType::Unit);
         match &final_type {
            ExpressionType::CompileError => (),
            ExpressionType::Struct(s_id, generic_args) => {
               let si = validation_context.user_defined_types.struct_info.get(*s_id).unwrap();

               validation_context
                  .source_to_definition
                  .insert(*base_ident_location, si.location);
               let defined_fields = &si.field_types;
               let mut unmatched_fields: HashSet<StrId> = defined_fields.keys().copied().collect();
               for field in fields.iter() {
                  // Extraneous field check
                  let Some(defined_type_node) = defined_fields.get(&field.0) else {
                     rolandc_error_w_details!(
                        err_manager,
                        &[(expr_location, "struct instantiated"), (si.location, "struct defined"),],
                        "`{}` is not a known field of struct `{}`",
                        validation_context.interner.lookup(field.0),
                        validation_context.interner.lookup(si.name),
                     );
                     continue;
                  };
                  let defined_type = map_generic_to_concrete_cow(
                     &defined_type_node.e_type,
                     generic_args,
                     validation_context
                        .templated_types
                        .get(&UserDefinedTypeId::Struct(*s_id))
                        .unwrap_or(&IndexSet::new()),
                  );

                  // Duplicate field check
                  if !unmatched_fields.remove(&field.0) {
                     rolandc_error_w_details!(
                        err_manager,
                        &[(expr_location, "struct instantiated"), (si.location, "struct defined"),],
                        "`{}` is a valid field of struct `{}`, but is duplicated",
                        validation_context.interner.lookup(field.0),
                        validation_context.interner.lookup(si.name),
                     );
                  }

                  if let Some(field_val) = field.1 {
                     let merged = try_merge_types(
                        &defined_type,
                        validation_context.ast.expressions[field_val].exp_type.as_ref().unwrap(),
                        &mut validation_context.owned.type_variables,
                     );
                     let field_expr = &validation_context.ast.expressions[field_val];

                     if !merged
                        && !field_expr
                           .exp_type
                           .as_ref()
                           .unwrap()
                           .is_or_contains_or_points_to_error()
                     {
                        let field_1_type_str = field_expr.exp_type.as_ref().unwrap().as_roland_type_info(
                           validation_context.interner,
                           validation_context.user_defined_types,
                           validation_context.procedures,
                           &validation_context.owned.type_variables,
                        );
                        let defined_type_str = defined_type.as_roland_type_info(
                           validation_context.interner,
                           validation_context.user_defined_types,
                           validation_context.procedures,
                           &validation_context.owned.type_variables,
                        );
                        rolandc_error_w_details!(
                           err_manager,
                           &[(field_expr.location, "field value"), (si.location, "struct defined"),],
                           "For field `{}` of struct `{}`, encountered value of type {} when we expected {}",
                           validation_context.interner.lookup(field.0),
                           validation_context.interner.lookup(si.name),
                           field_1_type_str,
                           defined_type_str,
                        );
                     }
                  }
               }

               // Missing field check
               if !unmatched_fields.is_empty() {
                  let unmatched_fields_str: Vec<&str> = unmatched_fields
                     .iter()
                     .map(|x| validation_context.interner.lookup(*x))
                     .collect();
                  rolandc_error_w_details!(
                     err_manager,
                     &[(expr_location, "struct instantiated"), (si.location, "struct defined"),],
                     "Literal of struct `{}` is missing fields [{}]",
                     validation_context.interner.lookup(si.name),
                     unmatched_fields_str.join(", "),
                  );
               }

               *expr = Expression::StructLiteral(*s_id, fields.iter().map(|x| (x.0, x.1)).collect());
            }
            _ => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempted to instantiate `{}` as a struct",
                  final_type.as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  ),
               );
            }
         }

         final_type
      }
      Expression::ProcedureCall { proc_expr, args } => {
         type_expression(err_manager, *proc_expr, validation_context);
         for arg in args.iter() {
            type_expression(err_manager, arg.expr, validation_context);
         }

         let mut the_type = validation_context.ast.expressions[*proc_expr].exp_type.take().unwrap();
         let resulting_type = match &mut the_type {
            ExpressionType::ProcedureItem(proc_id, generic_args) => {
               let proc = &validation_context.procedures[*proc_id];
               check_procedure_call(
                  args,
                  generic_args,
                  proc.definition.parameters.len(),
                  proc.definition.parameters.iter().map(|x| &x.p_type.e_type),
                  &proc.named_parameters,
                  &proc.type_parameters,
                  expr_location,
                  validation_context,
                  err_manager,
               );
               let mut resulting_type = proc.definition.ret_type.e_type.clone();
               map_generic_to_concrete(&mut resulting_type, generic_args, &proc.type_parameters);
               resulting_type
            }
            ExpressionType::ProcedurePointer { parameters, ret_type } => {
               check_procedure_call(
                  args,
                  &mut [],
                  parameters.len(),
                  parameters.iter(),
                  &HashMap::new(),
                  &IndexMap::new(),
                  expr_location,
                  validation_context,
                  err_manager,
               );
               ret_type.deref().deref().clone()
            }
            ExpressionType::CompileError => ExpressionType::CompileError,
            bad_type => {
               rolandc_error!(
                  err_manager,
                  validation_context.ast.expressions[*proc_expr].location,
                  "Attempting to invoke a procedure on non-procedure type {}",
                  bad_type.as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  ),
               );
               ExpressionType::CompileError
            }
         };
         validation_context.ast.expressions[*proc_expr].exp_type = Some(the_type);
         resulting_type
      }
      Expression::FieldAccess(field, lhs) => {
         let field = *field;
         type_expression(err_manager, *lhs, validation_context);

         let lhs = &validation_context.ast.expressions[*lhs];
         let mut lhs_type = lhs.exp_type.as_ref().unwrap().clone();

         let length_token = validation_context.interner.reverse_lookup("length");

         match lhs_type {
            ExpressionType::Struct(struct_id, generic_args) => {
               let si = validation_context
                  .user_defined_types
                  .struct_info
                  .get(struct_id)
                  .unwrap();
               if let Some(new_t_node) = si.field_types.get(&field) {
                  lhs_type = new_t_node.e_type.clone();
                  if let Some(generic_params) = validation_context
                     .templated_types
                     .get(&UserDefinedTypeId::Struct(struct_id))
                  {
                     map_generic_to_concrete(&mut lhs_type, &generic_args, generic_params);
                  }
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_location,
                     "Struct `{}` does not have a field `{}`",
                     validation_context.interner.lookup(si.name),
                     validation_context.interner.lookup(field),
                  );
                  lhs_type = ExpressionType::CompileError;
               }
            }
            ExpressionType::Union(union_id, generic_args) => {
               let ui = validation_context.user_defined_types.union_info.get(union_id).unwrap();
               if let Some(new_t_node) = ui.field_types.get(&field) {
                  lhs_type = new_t_node.e_type.clone();
                  if let Some(generic_params) = validation_context
                     .templated_types
                     .get(&UserDefinedTypeId::Union(union_id))
                  {
                     map_generic_to_concrete(&mut lhs_type, &generic_args, generic_params);
                  }
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_location,
                     "Union `{}` does not have a field `{}`",
                     validation_context.interner.lookup(ui.name),
                     validation_context.interner.lookup(field),
                  );
                  lhs_type = ExpressionType::CompileError;
               }
            }
            ExpressionType::Array(_, _) => {
               if Some(field) == length_token {
                  lhs_type = USIZE_TYPE;
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_location,
                     "Array does not have a field `{}`. Hint: Array types have a single field `length`",
                     validation_context.interner.lookup(field),
                  );
                  lhs_type = ExpressionType::CompileError;
               }
            }
            ExpressionType::CompileError => {
               lhs_type = ExpressionType::CompileError;
            }
            other_type => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Encountered field access on type {}; only structs, unions, and arrays have fields",
                  other_type.as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  )
               );
               lhs_type = ExpressionType::CompileError;
            }
         }

         lhs_type
      }
      Expression::ArrayLiteral(elems) => {
         for elem in elems.iter() {
            type_expression(err_manager, *elem, validation_context);
         }

         let mut any_error = false;

         for i in 1..elems.len() {
            let merged = try_merge_types_of_two_distinct_expressions(
               elems[i - 1],
               elems[i],
               &validation_context.ast.expressions,
               &mut validation_context.owned.type_variables,
            );

            let last_elem_expr = &validation_context.ast.expressions[elems[i - 1]];
            let this_elem_expr = &validation_context.ast.expressions[elems[i]];

            if last_elem_expr
               .exp_type
               .as_ref()
               .unwrap()
               .is_or_contains_or_points_to_error()
               || this_elem_expr
                  .exp_type
                  .as_ref()
                  .unwrap()
                  .is_or_contains_or_points_to_error()
            {
               // avoid cascading errors
            } else if !merged {
               rolandc_error_w_details!(
                  err_manager,
                  &[
                     (expr_location, "array literal".into()),
                     (last_elem_expr.location, format!("element {}", i - 1)),
                     (this_elem_expr.location, format!("element {}", i))
                  ],
                  "Element at array index {} has type of {}, but element at array index {} has mismatching type of {}",
                  i - 1,
                  last_elem_expr.exp_type.as_ref().unwrap().as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  ),
                  i,
                  this_elem_expr.exp_type.as_ref().unwrap().as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  ),
               );
               any_error = true;
            }
         }

         // @U32Arrays
         let max_elems = u32::MAX as usize;
         if elems.len() > max_elems {
            any_error = true;
            rolandc_error!(
               err_manager,
               expr_location,
               "Array literal has {} elements, which is more than the maximum {} elements",
               elems.len(),
               max_elems,
            );
         }

         if any_error {
            ExpressionType::CompileError
         } else if elems.is_empty() {
            let new_type_variable = validation_context
               .owned
               .type_variables
               .new_type_variable(TypeConstraint::None);
            ExpressionType::Array(Box::new(ExpressionType::Unknown(new_type_variable)), 0)
         } else {
            // We specifically want to type the array with the last element, because we have accumulated type information while iterating the literal
            // For instance: [2, 2, 2u8, 3]
            // In this example, the first element will have a type variable that should resolve to u8, but the last element will already be u8
            let a_type = validation_context.ast.expressions[*elems.last().unwrap()]
               .exp_type
               .clone()
               .unwrap();
            let t_len = elems.len().try_into().unwrap(); // unwrap should always succeed due to error check above
            ExpressionType::Array(Box::new(a_type), t_len)
         }
      }
      Expression::ArrayIndex { array, index } => {
         type_expression(err_manager, *array, validation_context);
         type_expression(err_manager, *index, validation_context);

         // Typing the index
         {
            let merged = try_merge_types(
               &USIZE_TYPE,
               validation_context.ast.expressions[*index].exp_type.as_ref().unwrap(),
               &mut validation_context.owned.type_variables,
            );

            let index_expression = &validation_context.ast.expressions[*index];
            if index_expression
               .exp_type
               .as_ref()
               .unwrap()
               .is_or_contains_or_points_to_error()
            {
               // avoid cascading errors
            } else if !merged {
               rolandc_error!(
                  err_manager,
                  index_expression.location,
                  "Attempted to index an array with a value of type {}, which is not usize",
                  index_expression.exp_type.as_ref().unwrap().as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  ),
               );
            }
         }

         let array_expression = &mut validation_context.ast.expressions[*array];
         lower_unknowns_in_type(
            array_expression.exp_type.as_mut().unwrap(),
            &validation_context.owned.type_variables,
         );
         match &array_expression.exp_type {
            Some(x) if x.is_or_contains_or_points_to_error() => ExpressionType::CompileError,
            Some(ExpressionType::Array(b, _)) => b.deref().clone(),
            Some(x @ ExpressionType::Pointer(b)) if matches!(**b, ExpressionType::Array(_, _)) => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempted to index expression of type {}, which is not an array type. Hint: Dereference this pointer with ~",
                  x.as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  ),
               );

               ExpressionType::CompileError
            }
            Some(x) => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempted to index expression of type {}, which is not an array type",
                  x.as_roland_type_info(
                     validation_context.interner,
                     validation_context.user_defined_types,
                     validation_context.procedures,
                     &validation_context.owned.type_variables
                  ),
               );

               ExpressionType::CompileError
            }
            None => unreachable!(),
         }
      }
      Expression::UnresolvedEnumLiteral(x, v) => match validation_context.user_defined_type_name_table.get(&x.str) {
         Some(UserDefinedTypeId::Struct(_)) => {
            rolandc_error!(
               err_manager,
               x.location,
               "Attempted to instantiate struct `{}` as an enum",
               validation_context.interner.lookup(x.str),
            );
            ExpressionType::CompileError
         }
         Some(UserDefinedTypeId::Union(_)) => {
            rolandc_error!(
               err_manager,
               x.location,
               "Attempted to instantiate union `{}` as an enum",
               validation_context.interner.lookup(x.str),
            );
            ExpressionType::CompileError
         }
         Some(UserDefinedTypeId::Enum(eid)) => {
            let enum_info = validation_context.user_defined_types.enum_info.get(*eid).unwrap();
            validation_context
               .source_to_definition
               .insert(x.location, enum_info.location);
            if let Some(variant_location) = enum_info.variants.get(&v.str) {
               validation_context
                  .source_to_definition
                  .insert(v.location, *variant_location);
               *expr = Expression::EnumLiteral(*eid, v.str);
               ExpressionType::Enum(*eid)
            } else {
               rolandc_error!(
                  err_manager,
                  v.location,
                  "Attempted to instantiate unknown variant `{}` of enum `{}`",
                  validation_context.interner.lookup(v.str),
                  validation_context.interner.lookup(x.str),
               );

               ExpressionType::CompileError
            }
         }
         None => {
            rolandc_error!(
               err_manager,
               x.location,
               "Attempted to instantiate enum `{}`, which does not exist",
               validation_context.interner.lookup(x.str),
            );

            ExpressionType::CompileError
         }
      },
      Expression::IfX(a, b, c) => {
         type_expression(err_manager, *a, validation_context);
         type_expression(err_manager, *b, validation_context);
         type_expression(err_manager, *c, validation_context);

         let merged = try_merge_types_of_two_distinct_expressions(
            *b,
            *c,
            &validation_context.ast.expressions,
            &mut validation_context.owned.type_variables,
         );

         let en = &validation_context.ast.expressions[*a];
         let is_bool = try_merge_types(
            &ExpressionType::Bool,
            en.exp_type.as_ref().unwrap(),
            &mut validation_context.owned.type_variables,
         );
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if !is_bool && !if_exp_type.is_or_contains_or_points_to_error() {
            rolandc_error!(
               err_manager,
               en.location,
               "Type of ifx condition must be a bool; got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
         }

         let then_expr = &validation_context.ast.expressions[*b];
         let then_type = then_expr.exp_type.as_ref().unwrap();
         let else_expr = &validation_context.ast.expressions[*c];
         let else_type = else_expr.exp_type.as_ref().unwrap();
         if then_type.is_never() {
            else_type.clone()
         } else if else_type.is_never() || merged {
            then_type.clone()
         } else {
            rolandc_error_w_details!(
               err_manager,
               &[
                  (then_expr.location, "then expression"),
                  (else_expr.location, "else expression")
               ],
               "ifx requires then and else expressions to have identical types; instead got {} and {}",
               then_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               ),
               else_type.as_roland_type_info(
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables
               )
            );
            ExpressionType::CompileError
         }
      }
      Expression::Variable(var_id) => validation_context
         .owned
         .cur_procedure_locals
         .get(var_id)
         .or_else(|| validation_context.global_info.get(var_id).map(|x| &x.expr_type.e_type))
         .cloned()
         .unwrap(),
      Expression::StructLiteral(_, _) | Expression::EnumLiteral(_, _) => unreachable!(),
   }
}

fn check_procedure_call<'a, I>(
   args: &[ArgumentNode],
   generic_args: &mut [ExpressionType],
   num_parameters: usize,
   parameters: I,
   named_parameters: &HashMap<StrId, ExpressionType>,
   generic_parameters: &IndexMap<StrId, IndexSet<StrId>>,
   call_location: SourceInfo,
   validation_context: &mut ValidationContext,
   err_manager: &mut ErrorManager,
) where
   I: IntoIterator<Item = &'a ExpressionType>,
{
   // Validate that there are no positional arguments after named arguments
   let first_named_arg = args.iter().enumerate().find(|(_, arg)| arg.name.is_some()).map(|x| x.0);
   let last_normal_arg = args
      .iter()
      .enumerate()
      .rfind(|(_, arg)| arg.name.is_none())
      .map(|x| x.0);
   let args_in_order = first_named_arg
      .and_then(|x| last_normal_arg.map(|y| x > y))
      .unwrap_or(true);

   if !args_in_order {
      rolandc_error!(
         err_manager,
         call_location,
         "Procedure call has named argument(s) which come before non-named argument(s)",
      );
   }

   if args_in_order && num_parameters != args.len() {
      rolandc_error!(
         err_manager,
         call_location,
         "Mismatched arity for procedure call. Expected {} arguments but got {}",
         num_parameters,
         args.len()
      );
      // We shortcircuit here, because there will likely be lots of mismatched types if an arg was forgotten
   } else if args_in_order {
      for (i, (actual, expected_raw)) in args.iter().zip(parameters.into_iter()).enumerate() {
         // These should be at the end by now, so we've checked everything we needed to
         if actual.name.is_some() {
            break;
         }

         let expected = map_generic_to_concrete_cow(expected_raw, generic_args, generic_parameters);

         let merged = try_merge_types(
            &expected,
            validation_context.ast.expressions[actual.expr]
               .exp_type
               .as_ref()
               .unwrap(),
            &mut validation_context.owned.type_variables,
         );

         let actual_expr = &validation_context.ast.expressions[actual.expr];
         let actual_type = actual_expr.exp_type.as_ref().unwrap();

         if !merged && !actual_type.is_or_contains_or_points_to_error() {
            let actual_type_str = actual_type.as_roland_type_info(
               validation_context.interner,
               validation_context.user_defined_types,
               validation_context.procedures,
               &validation_context.owned.type_variables,
            );
            let expected_type_str = expected.as_roland_type_info(
               validation_context.interner,
               validation_context.user_defined_types,
               validation_context.procedures,
               &validation_context.owned.type_variables,
            );
            rolandc_error!(
               err_manager,
               actual_expr.location,
               "Argument at position {} is of type {} when we expected {}",
               i,
               actual_type_str,
               expected_type_str,
            );
         }
      }

      for arg in args.iter().filter(|x| x.name.is_some()) {
         let expected_raw = named_parameters.get(&arg.name.unwrap());

         if expected_raw.is_none() {
            rolandc_error!(
               err_manager,
               call_location,
               "Encountered named argument `{}` that does not correspond to any named parameter",
               validation_context.interner.lookup(arg.name.unwrap()),
            );
            continue;
         }

         let expected = map_generic_to_concrete_cow(expected_raw.as_ref().unwrap(), generic_args, generic_parameters);

         let merged = try_merge_types(
            &expected,
            validation_context.ast.expressions[arg.expr].exp_type.as_ref().unwrap(),
            &mut validation_context.owned.type_variables,
         );

         let arg_expr = &validation_context.ast.expressions[arg.expr];

         let actual_type = arg_expr.exp_type.as_ref().unwrap();
         if !merged && !actual_type.is_or_contains_or_points_to_error() {
            let actual_type_str = actual_type.as_roland_type_info(
               validation_context.interner,
               validation_context.user_defined_types,
               validation_context.procedures,
               &validation_context.owned.type_variables,
            );
            let expected_type_str = expected.as_roland_type_info(
               validation_context.interner,
               validation_context.user_defined_types,
               validation_context.procedures,
               &validation_context.owned.type_variables,
            );
            rolandc_error!(
               err_manager,
               arg_expr.location,
               "Encountered argument of type {} when we expected {} for named parameter {}",
               actual_type_str,
               expected_type_str,
               validation_context.interner.lookup(arg.name.unwrap())
            );
         }
      }
   }
}

#[must_use]
fn check_procedure_item(
   callee_proc_id: ProcedureId,
   callee_proc_name: StrId,
   callee_type_params: &IndexMap<StrId, IndexSet<StrId>>,
   location: SourceInfo,
   type_arguments: &[ExpressionTypeNode],
   interner: &Interner,
   udt: &UserDefinedTypeInfo,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   err_manager: &mut ErrorManager,
   type_variable_info: &mut TypeVariableManager,
) -> (ExpressionType, bool) {
   if callee_type_params.len() != type_arguments.len() {
      rolandc_error!(
         err_manager,
         location,
         "Mismatched arity for procedure '{}'. Expected {} type arguments but got {}",
         interner.lookup(callee_proc_name),
         callee_type_params.len(),
         type_arguments.len()
      );
      return (ExpressionType::CompileError, false);
   }
   let mut type_arguments_are_valid = true;
   for (g_arg, constraints) in type_arguments.iter().zip(callee_type_params.values()) {
      match g_arg.e_type {
         ExpressionType::Unresolved {
            name: _,
            generic_args: _,
         } => {
            // We have already errored on this argument
            type_arguments_are_valid = false;
         }
         _ => {
            for constraint in constraints {
               let tc = match interner.lookup(*constraint) {
                  "Enum" => TypeConstraint::Enum,
                  "Float" => TypeConstraint::Float,
                  _ => unreachable!(),
               };
               if !constraint_matches_type_or_try_constrain(tc, &g_arg.e_type, type_variable_info) {
                  rolandc_error!(
                     err_manager,
                     g_arg.location,
                     "For procedure `{}`, encountered type argument of type {} which does not meet the constraint `{}`",
                     interner.lookup(callee_proc_name),
                     g_arg
                        .e_type
                        .as_roland_type_info(interner, udt, procedures, type_variable_info),
                     interner.lookup(*constraint),
                  );
                  type_arguments_are_valid = false;
               }
            }
         }
      }
   }
   (
      ExpressionType::ProcedureItem(
         callee_proc_id,
         type_arguments
            .iter()
            .map(|x| x.e_type.clone())
            .collect::<Vec<_>>()
            .into_boxed_slice(),
      ),
      type_arguments_are_valid,
   )
}

fn error_type_declared_vs_actual(
   declared: &ExpressionTypeNode,
   actual: &ExpressionNode,
   interner: &Interner,
   udt: &UserDefinedTypeInfo,
   procedures: &SlotMap<ProcedureId, ProcedureNode>,
   type_variable_info: &TypeVariableManager,
   err_manager: &mut ErrorManager,
) {
   fn address_of_actual_matches_dt(actual_type: &ExpressionType, declared_type: &ExpressionType) -> bool {
      deref_of_actual_matches_dt(declared_type, actual_type)
   }
   fn deref_of_actual_matches_dt(actual_type: &ExpressionType, declared_type: &ExpressionType) -> bool {
      match actual_type {
         ExpressionType::Pointer(inner) => inner.as_ref() == declared_type,
         _ => false,
      }
   }

   let actual_type = actual.exp_type.as_ref().unwrap();
   let declared_type = &declared.e_type;
   // TODO: this never type check should be part of the core type system (try_merge_types)
   // checking it here is a weird special case and it will not work with unknowns that resolved to unknown (rare but possible)
   if !actual_type.is_or_contains_or_points_to_error() && !actual_type.is_never() {
      let actual_type_str = actual_type.as_roland_type_info(interner, udt, procedures, type_variable_info);
      let declared_type_str = declared
         .e_type
         .as_roland_type_info(interner, udt, procedures, type_variable_info);
      let locations = &[(actual.location, "expression"), (declared.location, "declared type")];

      if address_of_actual_matches_dt(actual_type, declared_type) {
         rolandc_error_w_details!(
            err_manager,
            locations,
            "Declared type {} does not match actual expression type {}. Hint: Take the address of this expression using &",
            declared_type_str,
            actual_type_str,
         );
      } else if deref_of_actual_matches_dt(actual_type, declared_type) {
         rolandc_error_w_details!(
            err_manager,
            locations,
            "Declared type {} does not match actual expression type {}. Hint: Dereference this expression using ~",
            declared_type_str,
            actual_type_str,
         );
      } else if matches!(declared_type, ExpressionType::ProcedurePointer { .. })
         && matches!(actual_type, ExpressionType::ProcedureItem(_, _))
      {
         rolandc_error_w_details!(
            err_manager,
            locations,
            "Declared type {} does not match actual expression type {}. Hint: Procedures must be cast to procedure pointers using &",
            declared_type_str,
            actual_type_str,
         );
      } else {
         rolandc_error_w_details!(
            err_manager,
            locations,
            "Declared type {} does not match actual expression type {}",
            declared_type_str,
            actual_type_str,
         );
      }
   }
}

pub fn map_generic_to_concrete_cow<'a, T>(
   param_type: &'a ExpressionType,
   generic_args: &[ExpressionType],
   generic_parameters: &T,
) -> Cow<'a, ExpressionType>
where
   T: CanCheckContainsStrId,
{
   if generic_args.is_empty() {
      Cow::Borrowed(param_type)
   } else {
      let mut new = param_type.clone();
      map_generic_to_concrete(&mut new, generic_args, generic_parameters);
      Cow::Owned(new)
   }
}

pub fn map_generic_to_concrete<T>(
   param_type: &mut ExpressionType,
   generic_args: &[ExpressionType],
   generic_parameters: &T,
) where
   T: CanCheckContainsStrId,
{
   match param_type {
      ExpressionType::Array(inner_type, _) | ExpressionType::Pointer(inner_type) => {
         map_generic_to_concrete(inner_type, generic_args, generic_parameters);
      }
      ExpressionType::ProcedurePointer { parameters, ret_type } => {
         for param in parameters.iter_mut() {
            map_generic_to_concrete(param, generic_args, generic_parameters);
         }
         map_generic_to_concrete(ret_type, generic_args, generic_parameters);
      }
      ExpressionType::ProcedureItem(_, type_params) => {
         for type_param in type_params.iter_mut() {
            map_generic_to_concrete(type_param, generic_args, generic_parameters);
         }
      }
      ExpressionType::Struct(_, type_arguments) | ExpressionType::Union(_, type_arguments) => {
         for type_argument in type_arguments.iter_mut() {
            map_generic_to_concrete(type_argument, generic_args, generic_parameters);
         }
      }
      ExpressionType::GenericParam(x) => {
         let generic_param_index = generic_parameters.get_index_of(*x).unwrap();
         *param_type = generic_args[generic_param_index].clone();
      }
      _ => (),
   }
}

pub fn check_globals(
   program: &mut Program,
   owned_validation_context: &mut OwnedValidationContext,
   interner: &mut Interner,
   err_manager: &mut ErrorManager,
) {
   let mut validation_context = ValidationContext {
      owned: owned_validation_context,
      source_to_definition: &mut program.source_to_definition,
      next_var_dont_access: &mut program.next_variable,
      interner,
      ast: &mut program.ast,
      procedures: &program.procedures,
      proc_name_table: &program.procedure_name_table,
      user_defined_type_name_table: &program.user_defined_type_name_table,
      user_defined_types: &mut program.user_defined_types,
      global_info: &mut program.non_stack_var_info,
      templated_types: &program.templated_types,
   };

   // Populate variable resolution with globals
   for gi in validation_context.global_info.iter() {
      validation_context.owned.variable_types.insert(
         gi.1.name,
         VariableDetails {
            declaration_location: gi.1.location,
            kind: VariableScopeKind::Global,
            used: false,
            var_id: *gi.0,
         },
      );
   }

   let initializers: Vec<ExpressionId> = validation_context
      .global_info
      .values()
      .filter_map(|x| x.initializer)
      .collect();
   for initializer in initializers {
      type_expression(err_manager, initializer, &mut validation_context);
   }

   for p_global in validation_context
      .global_info
      .values()
      .filter(|x| x.initializer.is_some())
   {
      let merged = try_merge_types(
         &p_global.expr_type.e_type,
         validation_context.ast.expressions[p_global.initializer.unwrap()]
            .exp_type
            .as_ref()
            .unwrap(),
         &mut validation_context.owned.type_variables,
      );

      if !merged {
         let p_static_expr = &validation_context.ast.expressions[p_global.initializer.unwrap()];

         error_type_declared_vs_actual(
            &p_global.expr_type,
            p_static_expr,
            validation_context.interner,
            validation_context.user_defined_types,
            validation_context.procedures,
            &validation_context.owned.type_variables,
            err_manager,
         );
      }
   }
}

fn try_merge_types_of_two_distinct_expressions(
   a: ExpressionId,
   b: ExpressionId,
   ast: &ExpressionPool,
   type_variables: &mut TypeVariableManager,
) -> bool {
   try_merge_types(
      ast[a].exp_type.as_ref().unwrap(),
      ast[b].exp_type.as_ref().unwrap(),
      type_variables,
   )
}

fn well_typed(et: &mut ExpressionType, type_variables: &TypeVariableManager) -> bool {
   lower_unknowns_in_type(et, type_variables);
   match et {
      ExpressionType::Unknown(_)
      | ExpressionType::CompileError
      | ExpressionType::GenericParam(_)
      | ExpressionType::Unresolved { .. } => false,
      ExpressionType::Pointer(v) | ExpressionType::Array(v, _) => well_typed(v, type_variables),
      ExpressionType::ProcedureItem(_, type_args)
      | ExpressionType::Struct(_, type_args)
      | ExpressionType::Union(_, type_args) => type_args.iter_mut().all(|t| well_typed(t, type_variables)),
      ExpressionType::ProcedurePointer { parameters, ret_type } => parameters
         .iter_mut()
         .chain(std::iter::once(ret_type.as_mut()))
         .all(|t| well_typed(t, type_variables)),
      ExpressionType::Never
      | ExpressionType::Int(_)
      | ExpressionType::Float(_)
      | ExpressionType::Bool
      | ExpressionType::Unit
      | ExpressionType::Enum(_) => true,
   }
}

fn tree_is_well_typed(
   expr_id: ExpressionId,
   expressions: &mut ExpressionPool,
   type_variable_info: &TypeVariableManager,
) -> bool {
   let mut the_expr = std::mem::replace(&mut expressions[expr_id].expression, Expression::UnitLiteral);
   let children_ok = match &mut the_expr {
      Expression::ProcedureCall { proc_expr, args } => args
         .iter_mut()
         .map(|x| x.expr)
         .chain(std::iter::once(*proc_expr))
         .all(|x| tree_is_well_typed(x, expressions, type_variable_info)),
      Expression::ArrayLiteral(expression_ids) => expression_ids
         .iter_mut()
         .all(|x| tree_is_well_typed(*x, expressions, type_variable_info)),
      Expression::BinaryOperator { operator: _, lhs, rhs } | Expression::ArrayIndex { array: lhs, index: rhs } => {
         tree_is_well_typed(*lhs, expressions, type_variable_info)
            && tree_is_well_typed(*rhs, expressions, type_variable_info)
      }
      Expression::UnaryOperator(_, expression_id) | Expression::FieldAccess(_, expression_id) => {
         tree_is_well_typed(*expression_id, expressions, type_variable_info)
      }
      Expression::StructLiteral(_, vals) => vals
         .values()
         .flatten()
         .all(|x| tree_is_well_typed(*x, expressions, type_variable_info)),
      Expression::Cast {
         cast_type: _,
         target_type,
         expr,
      } => well_typed(target_type, type_variable_info) && tree_is_well_typed(*expr, expressions, type_variable_info),
      Expression::BoundFcnLiteral(_, expression_type_nodes) => expression_type_nodes
         .iter_mut()
         .map(|x| &mut x.e_type)
         .all(|t| well_typed(t, type_variable_info)),
      Expression::IfX(a, b, c) => {
         tree_is_well_typed(*a, expressions, type_variable_info)
            && tree_is_well_typed(*b, expressions, type_variable_info)
            && tree_is_well_typed(*c, expressions, type_variable_info)
      }
      Expression::UnresolvedStructLiteral(_, _, _)
      | Expression::UnresolvedVariable(_)
      | Expression::UnresolvedEnumLiteral(_, _)
      | Expression::UnresolvedProcLiteral(_, _) => false,
      Expression::Variable(_)
      | Expression::EnumLiteral(_, _)
      | Expression::BoolLiteral(_)
      | Expression::StringLiteral(_)
      | Expression::IntLiteral { .. }
      | Expression::FloatLiteral(_)
      | Expression::UnitLiteral => true,
   };
   expressions[expr_id].expression = the_expr;
   children_ok && well_typed(expressions[expr_id].exp_type.as_mut().unwrap(), type_variable_info)
}

fn fold_expr_id(expr_id: ExpressionId, err_manager: &mut ErrorManager, validation_context: &mut ValidationContext) {
   if !tree_is_well_typed(
      expr_id,
      &mut validation_context.ast.expressions,
      &validation_context.owned.type_variables,
   ) {
      return;
   }
   let current_proc_name = validation_context
      .owned
      .cur_procedure
      .map(|x| validation_context.procedures[x].definition.name.str);
   let mut fc = FoldingContext {
      ast: validation_context.ast,
      procedures: validation_context.procedures,
      user_defined_types: validation_context.user_defined_types,
      const_replacements: &HashMap::new(),
      current_proc_name,
      target: validation_context.owned.target,
      templated_types: validation_context.templated_types,
   };
   constant_folding::try_fold_and_replace_expr(expr_id, &mut Some(err_manager), &mut fc, validation_context.interner);
}
