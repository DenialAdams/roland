use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::ops::Deref;
use std::sync::OnceLock;

use indexmap::{IndexMap, IndexSet};
use slotmap::SlotMap;

use super::type_inference::try_set_inferred_type;
use super::type_variables::{TypeConstraint, TypeVariableManager};
use super::{GlobalInfo, OwnedValidationContext, ValidationContext, VariableDetails, VariableScopeKind};
use crate::error_handling::error_handling_macros::{
   rolandc_error, rolandc_error_no_loc, rolandc_error_w_details, rolandc_warn,
};
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{
   statement_always_or_never_returns, ArgumentNode, BinOp, BlockNode, CastType, DeclarationValue, Expression,
   ExpressionId, ExpressionNode, ExpressionTypeNode, ProcImplSource, ProcedureId, ProcedureNode, Program, Statement,
   StatementId, StrNode, UnOp, UserDefinedTypeId, UserDefinedTypeInfo, VariableId,
};
use crate::size_info::{mem_alignment, sizeof_type_mem};
use crate::source_info::SourceInfo;
use crate::type_data::{ExpressionType, IntType, F32_TYPE, F64_TYPE, I32_TYPE, U32_TYPE, U64_TYPE, USIZE_TYPE};
use crate::Target;

pub struct SpecialProcedure {
   pub name: StrId,
   pub required: bool,
   pub input_types: Vec<ExpressionType>,
   pub return_type: ExpressionType,
}

pub fn get_special_procedures(target: Target, interner: &mut Interner) -> &'static [SpecialProcedure] {
   static WASM4_SPECIAL: OnceLock<Box<[SpecialProcedure]>> = OnceLock::new();
   static WASI_AMD64_SPECIAL: OnceLock<Box<[SpecialProcedure]>> = OnceLock::new();
   static MICROW8_SPECIAL: OnceLock<Box<[SpecialProcedure]>> = OnceLock::new();
   match target {
      Target::Lib => &[],
      Target::Wasm4 => WASM4_SPECIAL.get_or_init(|| {
         Box::new([
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
         ])
      }),
      Target::Wasi | Target::Qbe => WASI_AMD64_SPECIAL.get_or_init(|| {
         Box::new([SpecialProcedure {
            name: interner.intern("main"),
            required: true,
            input_types: vec![],
            return_type: ExpressionType::Unit,
         }])
      }),
      Target::Microw8 => MICROW8_SPECIAL.get_or_init(|| {
         Box::new([
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
         ])
      }),
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
}

impl<V> CanCheckContainsStrId for IndexMap<StrId, V> {
   fn contains(&self, x: StrId) -> bool {
      self.contains_key(&x)
   }
}

impl CanCheckContainsStrId for IndexSet<StrId> {
   fn contains(&self, x: StrId) -> bool {
      self.contains(&x)
   }
}

impl CanCheckContainsStrId for () {
    fn contains(&self, _: StrId) -> bool {
        false
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
) -> bool where T: CanCheckContainsStrId {
   match v_type {
      ExpressionType::Pointer(vt) => resolve_type(
         vt,
         type_name_table,
         type_params,
         specialized_types,
         err_manager,
         interner,
         location_for_error,
      ),
      ExpressionType::Array(exp, _) => resolve_type(
         exp,
         type_name_table,
         type_params,
         specialized_types,
         err_manager,
         interner,
         location_for_error,
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
      | ExpressionType::Struct(_)
      | ExpressionType::Union(_)
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
            Some(UserDefinedTypeId::Union(y)) => ExpressionType::Union(*y),
            Some(UserDefinedTypeId::Struct(y)) => ExpressionType::Struct(*y),
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
               } else if type_params.map_or(false, |tp| tp.contains(*x)) {
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
) -> Vec<(ProcedureId, Box<[ExpressionType]>)> {
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
   };

   for id in procedures_to_check.iter().copied() {
      let proc = &program.procedures[id];
      let body = &mut program.procedure_bodies[id];
      validation_context.owned.cur_procedure = Some(id);
      let num_globals = validation_context.owned.variable_types.len();

      for parameter in proc.definition.parameters.iter() {
         validation_context.owned.variable_types.insert(
            parameter.name,
            VariableDetails {
               var_type: parameter.p_type.e_type.clone(),
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
   }
   validation_context.owned.cur_procedure = None;

   std::mem::take(&mut validation_context.owned.procedures_to_specialize)
}

fn type_statement(err_manager: &mut ErrorManager, statement: StatementId, validation_context: &mut ValidationContext) {
   let stmt_loc = validation_context.ast.statements[statement].location;

   let mut the_statement = std::mem::replace(
      &mut validation_context.ast.statements[statement].statement,
      Statement::Break,
   );
   match &mut the_statement {
      Statement::Assignment(lhs, rhs) => {
         type_expression(err_manager, *lhs, validation_context);
         type_expression(err_manager, *rhs, validation_context);

         try_set_inferred_type(
            &validation_context.ast.expressions[*lhs].exp_type.clone().unwrap(),
            *rhs,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         try_set_inferred_type(
            &validation_context.ast.expressions[*rhs].exp_type.clone().unwrap(),
            *lhs,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         let len = &validation_context.ast.expressions[*lhs];
         let en = &validation_context.ast.expressions[*rhs];

         let lhs_type = len.exp_type.as_ref().unwrap();
         let rhs_type = en.exp_type.as_ref().unwrap();

         if lhs_type.is_or_contains_or_points_to_error() || rhs_type.is_or_contains_or_points_to_error() {
            // avoid cascading errors
         } else if lhs_type != rhs_type && !rhs_type.is_never() {
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
            rolandc_error!(err_manager, stmt_loc, "Continue statement can only be used in a loop");
         }
      }
      Statement::Break => {
         if validation_context.owned.loop_depth == 0 {
            rolandc_error!(err_manager, stmt_loc, "Break statement can only be used in a loop");
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

         for expr_id in [*start, *end] {
            if let Some(x) = validation_context.ast.expressions[expr_id]
               .exp_type
               .as_ref()
               .unwrap()
               .get_type_variable_of_unknown_type()
            {
               let tvd = validation_context.owned.type_variables.get_data_mut(x);
               let _ = tvd.add_constraint(TypeConstraint::Int); // we'll handle the type mismatch below
            }
         }

         try_set_inferred_type(
            &validation_context.ast.expressions[*start].exp_type.clone().unwrap(),
            *end,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );
         try_set_inferred_type(
            &validation_context.ast.expressions[*end].exp_type.clone().unwrap(),
            *start,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         let start_expr = &validation_context.ast.expressions[*start];
         let end_expr = &validation_context.ast.expressions[*end];

         let result_type = match (
            start_expr.exp_type.as_ref().unwrap(),
            end_expr.exp_type.as_ref().unwrap(),
         ) {
            (lhs, _) if lhs.is_or_contains_or_points_to_error() => ExpressionType::CompileError,
            (_, rhs) if rhs.is_or_contains_or_points_to_error() => ExpressionType::CompileError,
            (ExpressionType::Int(x), ExpressionType::Int(y)) if x == y => ExpressionType::Int(*x),
            (ExpressionType::Unknown(x), ExpressionType::Unknown(y)) if x == y => ExpressionType::Unknown(*x),
            _ => {
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
            }
         };

         if *inclusive {
            rolandc_error!(err_manager, stmt_loc, "Inclusive ranges are not currently supported.");
         }

         let vars_before = validation_context.owned.variable_types.len();
         *var_id = declare_variable(err_manager, var, result_type.clone(), validation_context);
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
         let cond_type = cond_node.exp_type.as_ref().unwrap();
         if cond_type != &ExpressionType::Bool && !cond_type.is_or_contains_or_points_to_error() {
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
      Statement::IfElse(en, block_1, block_2) => {
         type_block(err_manager, block_1, validation_context);
         type_statement(err_manager, *block_2, validation_context);
         type_expression(err_manager, *en, validation_context);

         let en = &validation_context.ast.expressions[*en];
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if if_exp_type != &ExpressionType::Bool && !if_exp_type.is_or_contains_or_points_to_error() {
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

         // Type Inference
         try_set_inferred_type(
            cur_procedure_ret,
            *en,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         let en = &validation_context.ast.expressions[*en];

         if !en.exp_type.as_ref().unwrap().is_or_contains_or_points_to_error()
            && !en.exp_type.as_ref().unwrap().is_never()
            && *en.exp_type.as_ref().unwrap() != *cur_procedure_ret
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

         let mut dt_is_unresolved = false;
         if let Some(v) = dt.as_mut() {
            let spec_params = validation_context
               .owned
               .cur_procedure
               .map(|x| &validation_context.procedures[x].specialized_type_parameters);
            if !resolve_type::<()>(
               &mut v.e_type,
               validation_context.user_defined_type_name_table,
               None,
               spec_params,
               err_manager,
               validation_context.interner,
               v.location,
            ) {
               dt_is_unresolved = true;
            } else if let DeclarationValue::Expr(enid) = opt_enid {
               try_set_inferred_type(
                  &v.e_type,
                  *enid,
                  validation_context.owned,
                  &mut validation_context.ast.expressions,
               );
            }
         };

         let opt_en = match opt_enid {
            DeclarationValue::Expr(enid) => Some(*enid),
            DeclarationValue::Uninit | DeclarationValue::None => None,
         };

         let result_type = if dt_is_unresolved {
            ExpressionType::CompileError
         } else if let Some(dt_val) = dt {
            if let Some(en) = opt_en {
               check_type_declared_vs_actual(
                  dt_val,
                  &validation_context.ast.expressions[en],
                  validation_context.interner,
                  validation_context.user_defined_types,
                  validation_context.procedures,
                  &validation_context.owned.type_variables,
                  err_manager,
               );
            }

            dt_val.e_type.clone()
         } else if let Some(en) = opt_en {
            validation_context.ast.expressions[en].exp_type.clone().unwrap()
         } else {
            rolandc_error!(
               err_manager,
               id.location,
               "Uninitialized variables must be declared with a type",
            );
            ExpressionType::CompileError
         };

         *var_id = declare_variable(err_manager, id, result_type.clone(), validation_context);

         if let Some(storage_kind) = storage {
            validation_context.global_info.insert(
               *var_id,
               GlobalInfo {
                  expr_type: ExpressionTypeNode {
                     // This location is _not_ right, but it's not used anywhere that matters right now.
                     // and getting the right location isn't easy. TODO
                     location: stmt_loc,
                     e_type: result_type,
                  },
                  initializer: opt_en,
                  location: stmt_loc,
                  kind: *storage_kind,
                  name: id.str,
               },
            );
         } else {
            validation_context
               .owned
               .cur_procedure_locals
               .insert(*var_id, result_type);
         }
      }
   }
   validation_context.ast.statements[statement].statement = the_statement;
}

#[must_use]
fn declare_variable(
   err_manager: &mut ErrorManager,
   id: &StrNode,
   var_type: ExpressionType,
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
         var_type,
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
            validation_context.ast.expressions[expr_index].exp_type = Some(var_info.var_type.clone());
            validation_context.ast.expressions[expr_index].expression = Expression::Variable(var_info.var_id);
            return;
         }
         None => {
            if let Some(proc_id) = validation_context.proc_name_table.get(&id.str).copied() {
               validation_context.ast.expressions[expr_index].expression =
                  Expression::BoundFcnLiteral(proc_id, Box::new([]));
            }
         }
      },
      Expression::UnresolvedProcLiteral(name, g_args) => {
         for g_arg in g_args.iter_mut() {
            let spec_params = validation_context
               .owned
               .cur_procedure
               .map(|x| &validation_context.procedures[x].specialized_type_parameters);
            resolve_type::<()>(
               &mut g_arg.e_type,
               validation_context.user_defined_type_name_table,
               None,
               spec_params,
               err_manager,
               validation_context.interner,
               g_arg.location,
            );
         }

         if let Some(proc_id) = validation_context.proc_name_table.get(&name.str).copied() {
            validation_context.ast.expressions[expr_index].expression =
               Expression::BoundFcnLiteral(proc_id, std::mem::take(g_args).into_boxed_slice());
         }
      }
      _ => (),
   }

   let mut the_expr = std::mem::replace(
      &mut validation_context.ast.expressions[expr_index].expression,
      Expression::UnitLiteral,
   );
   validation_context.ast.expressions[expr_index].exp_type = Some(get_type(
      &mut the_expr,
      expr_location,
      err_manager,
      expr_index,
      validation_context,
   ));
   validation_context.ast.expressions[expr_index].expression = the_expr;
}

fn get_type(
   expr: &mut Expression,
   expr_location: SourceInfo,
   err_manager: &mut ErrorManager,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
) -> ExpressionType {
   match expr {
      Expression::UnitLiteral => ExpressionType::Unit,
      Expression::BoolLiteral(_) => ExpressionType::Bool,
      Expression::IntLiteral { .. } => {
         validation_context.owned.unknown_literals.insert(expr_index);
         let new_type_variable = validation_context
            .owned
            .type_variables
            .new_type_variable(TypeConstraint::Int);
         ExpressionType::Unknown(new_type_variable)
      }
      Expression::FloatLiteral(_) => {
         validation_context.owned.unknown_literals.insert(expr_index);
         let new_type_variable = validation_context
            .owned
            .type_variables
            .new_type_variable(TypeConstraint::Float);
         ExpressionType::Unknown(new_type_variable)
      }
      Expression::StringLiteral(_) => ExpressionType::Struct(validation_context.owned.string_struct_id),
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

         if from_type_is_unknown_int {
            if *cast_type == CastType::Transmute && target_type.is_pointer() {
               try_set_inferred_type(
                  &USIZE_TYPE,
                  *expr_id,
                  validation_context.owned,
                  &mut validation_context.ast.expressions,
               );
            } else if *cast_type == CastType::Transmute && matches!(*target_type, F64_TYPE) {
               try_set_inferred_type(
                  &U64_TYPE,
                  *expr_id,
                  validation_context.owned,
                  &mut validation_context.ast.expressions,
               );
            } else if *cast_type == CastType::Transmute && matches!(*target_type, F32_TYPE) {
               try_set_inferred_type(
                  &U32_TYPE,
                  *expr_id,
                  validation_context.owned,
                  &mut validation_context.ast.expressions,
               );
            } else if *cast_type == CastType::Transmute && matches!(target_type, ExpressionType::Enum(_)) {
               let enum_base_type = match target_type {
                  ExpressionType::Enum(x) => {
                     &validation_context
                        .user_defined_types
                        .enum_info
                        .get(*x)
                        .unwrap()
                        .base_type
                  }
                  _ => unreachable!(),
               };
               try_set_inferred_type(
                  enum_base_type,
                  *expr_id,
                  validation_context.owned,
                  &mut validation_context.ast.expressions,
               );
            }
         };

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

               let size_source = sizeof_type_mem(
                  e_type,
                  validation_context.user_defined_types,
                  validation_context.owned.target,
               );
               let size_target = sizeof_type_mem(
                  target_type,
                  validation_context.user_defined_types,
                  validation_context.owned.target,
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
                        AlignOrUnknown::Alignment(mem_alignment(a_type, ctx.user_defined_types, ctx.owned.target))
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
                        e_type.as_roland_type_info(validation_context.interner, validation_context.user_defined_types, validation_context.procedures, &validation_context.owned.type_variables),
                        target_type.as_roland_type_info(validation_context.interner, validation_context.user_defined_types, validation_context.procedures, &validation_context.owned.type_variables),
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
                     e_type.as_roland_type_info(validation_context.interner, validation_context.user_defined_types, validation_context.procedures, &validation_context.owned.type_variables),
                     target_type.as_roland_type_info(validation_context.interner, validation_context.user_defined_types, validation_context.procedures, &validation_context.owned.type_variables),
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
            ],
            BinOp::BitwiseAnd | BinOp::BitwiseOr | BinOp::BitwiseXor => &[TypeValidator::AnyInt, TypeValidator::Bool],
            BinOp::BitwiseLeftShift | BinOp::BitwiseRightShift | BinOp::Remainder => &[TypeValidator::AnyInt],
         };

         try_set_inferred_type(
            &validation_context.ast.expressions[*lhs].exp_type.clone().unwrap(),
            *rhs,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );
         try_set_inferred_type(
            &validation_context.ast.expressions[*rhs].exp_type.clone().unwrap(),
            *lhs,
            validation_context.owned,
            &mut validation_context.ast.expressions,
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
         } else if lhs_type != rhs_type {
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

         let e = &validation_context.ast.expressions[*e];

         if *un_op == UnOp::AddressOf {
            if let ExpressionType::ProcedureItem(proc_id, bound_type_params) = e.exp_type.as_ref().unwrap() {
               // special case
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
         }

         if *un_op == UnOp::Negate {
            if let Some(x) = e.exp_type.as_ref().unwrap().get_type_variable_of_unknown_type() {
               let tvd = validation_context.owned.type_variables.get_data_mut(x);
               if tvd.constraint == TypeConstraint::Int {
                  // could be a float, or totally unknown
                  tvd.add_constraint(TypeConstraint::SignedInt).unwrap();
               }
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
      Expression::BoundFcnLiteral(id, type_arguments) => match validation_context.procedures.get(*id) {
         Some(proc) => {
            validation_context
               .source_to_definition
               .insert(proc.definition.name.location, proc.location);
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
            );

            if check_result.1 && !type_arguments.is_empty() {
               validation_context.owned.procedures_to_specialize.push((
                  *id,
                  type_arguments
                     .iter()
                     .map(|x| x.e_type.clone())
                     .collect::<Vec<_>>()
                     .into_boxed_slice(),
               ));
            }

            check_result.0
         }
         None => unreachable!(),
      },
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
      Expression::UnresolvedStructLiteral(struct_name, fields) => {
         for field_val in fields.iter().filter_map(|x| x.1) {
            type_expression(err_manager, field_val, validation_context);
         }

         match validation_context
            .user_defined_type_name_table
            .get(&struct_name.str)
            .copied()
         {
            Some(UserDefinedTypeId::Enum(_)) => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempted to instantiate enum `{}` as a struct",
                  validation_context.interner.lookup(struct_name.str),
               );
               ExpressionType::CompileError
            }
            Some(UserDefinedTypeId::Union(_)) => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempted to instantiate union `{}` as a struct",
                  validation_context.interner.lookup(struct_name.str),
               );
               ExpressionType::CompileError
            }
            Some(UserDefinedTypeId::Struct(defined_struct)) => {
               let si = validation_context
                  .user_defined_types
                  .struct_info
                  .get(defined_struct)
                  .unwrap();

               validation_context
                  .source_to_definition
                  .insert(struct_name.location, si.location);
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
                        validation_context.interner.lookup(struct_name.str),
                     );
                     continue;
                  };
                  let defined_type = &defined_type_node.e_type;

                  // Duplicate field check
                  if !unmatched_fields.remove(&field.0) {
                     rolandc_error_w_details!(
                        err_manager,
                        &[(expr_location, "struct instantiated"), (si.location, "struct defined"),],
                        "`{}` is a valid field of struct `{}`, but is duplicated",
                        validation_context.interner.lookup(field.0),
                        validation_context.interner.lookup(struct_name.str),
                     );
                  }

                  if let Some(field_val) = field.1 {
                     try_set_inferred_type(
                        defined_type,
                        field_val,
                        validation_context.owned,
                        &mut validation_context.ast.expressions,
                     );

                     let field_expr = &validation_context.ast.expressions[field_val];

                     if field_expr.exp_type.as_ref().unwrap() != defined_type
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
                           validation_context.interner.lookup(struct_name.str),
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
                     validation_context.interner.lookup(struct_name.str),
                     unmatched_fields_str.join(", "),
                  );
               }

               *expr = Expression::StructLiteral(defined_struct, fields.iter().map(|x| (x.0, x.1)).collect());

               ExpressionType::Struct(defined_struct)
            }
            None => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Encountered construction of undefined struct `{}`",
                  validation_context.interner.lookup(struct_name.str)
               );
               ExpressionType::CompileError
            }
         }
      }
      Expression::ProcedureCall { proc_expr, args } => {
         type_expression(err_manager, *proc_expr, validation_context);
         for arg in args.iter() {
            type_expression(err_manager, arg.expr, validation_context);
         }

         let the_type = validation_context.ast.expressions[*proc_expr].exp_type.take().unwrap();
         let resulting_type = match &the_type {
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
                  &[],
                  parameters.len(),
                  parameters.iter(),
                  &HashMap::new(),
                  &IndexMap::new(),
                  expr_location,
                  validation_context,
                  err_manager,
               );
               ret_type.deref().clone()
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
            ExpressionType::Struct(struct_id) => {
               let si = validation_context
                  .user_defined_types
                  .struct_info
                  .get(struct_id)
                  .unwrap();
               if let Some(new_t_node) = si.field_types.get(&field) {
                  lhs_type = new_t_node.e_type.clone();
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
            ExpressionType::Union(union_id) => {
               let ui = validation_context.user_defined_types.union_info.get(union_id).unwrap();
               if let Some(new_t_node) = ui.field_types.get(&field) {
                  lhs_type = new_t_node.e_type.clone();
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
            let borrowed_type = validation_context.ast.expressions[elems[i - 1]]
               .exp_type
               .take()
               .unwrap();
            try_set_inferred_type(
               &borrowed_type,
               elems[i],
               validation_context.owned,
               &mut validation_context.ast.expressions,
            );
            validation_context.ast.expressions[elems[i - 1]].exp_type = Some(borrowed_type);

            let borrowed_type = validation_context.ast.expressions[elems[i]].exp_type.take().unwrap();
            try_set_inferred_type(
               &borrowed_type,
               elems[i - 1],
               validation_context.owned,
               &mut validation_context.ast.expressions,
            );
            validation_context.ast.expressions[elems[i]].exp_type = Some(borrowed_type);

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
            } else if last_elem_expr.exp_type.as_ref().unwrap() != this_elem_expr.exp_type.as_ref().unwrap() {
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
            validation_context.owned.unknown_literals.insert(expr_index);
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

         try_set_inferred_type(
            &USIZE_TYPE,
            *index,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         let array_expression = &validation_context.ast.expressions[*array];
         let index_expression = &validation_context.ast.expressions[*index];

         if index_expression
            .exp_type
            .as_ref()
            .unwrap()
            .is_or_contains_or_points_to_error()
         {
            // avoid cascading errors
         } else if index_expression.exp_type.as_ref().unwrap() != &USIZE_TYPE {
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

         match &array_expression.exp_type {
            Some(x) if x.is_or_contains_or_points_to_error() => ExpressionType::CompileError,
            Some(ExpressionType::Array(b, _)) => b.deref().clone(),
            Some(x @ ExpressionType::Pointer(b)) if matches!(**b, ExpressionType::Array(_, _)) => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempted to index expression of type {}, which is not an array type. Hint: Dereference this pointer with ~",
                  x.as_roland_type_info(validation_context.interner, validation_context.user_defined_types, validation_context.procedures, &validation_context.owned.type_variables),
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

         try_set_inferred_type(
            &validation_context.ast.expressions[*b].exp_type.clone().unwrap(),
            *c,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );
         try_set_inferred_type(
            &validation_context.ast.expressions[*c].exp_type.clone().unwrap(),
            *b,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         let en = &validation_context.ast.expressions[*a];
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if if_exp_type != &ExpressionType::Bool && !if_exp_type.is_or_contains_or_points_to_error() {
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
         } else if else_type.is_never() || then_type == else_type {
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
      Expression::Variable(_) | Expression::StructLiteral(_, _) | Expression::EnumLiteral(_, _) => unreachable!(),
   }
}

fn check_procedure_call<'a, I>(
   args: &[ArgumentNode],
   generic_args: &[ExpressionType],
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

         try_set_inferred_type(
            &expected,
            actual.expr,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         let actual_expr = &validation_context.ast.expressions[actual.expr];
         let actual_type = actual_expr.exp_type.as_ref().unwrap();

         if *actual_type != *expected && !actual_type.is_or_contains_or_points_to_error() {
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

         try_set_inferred_type(
            &expected,
            arg.expr,
            validation_context.owned,
            &mut validation_context.ast.expressions,
         );

         let arg_expr = &validation_context.ast.expressions[arg.expr];

         let actual_type = arg_expr.exp_type.as_ref().unwrap();
         if *actual_type != *expected && !actual_type.is_or_contains_or_points_to_error() {
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
               let constraint_met = match interner.lookup(*constraint) {
                  "Enum" => matches!(g_arg.e_type, ExpressionType::Enum(_)),
                  "Float" => matches!(g_arg.e_type, ExpressionType::Float(_)),
                  _ => unreachable!(),
               };
               if !constraint_met {
                  rolandc_error!(
                     err_manager,
                     g_arg.location,
                     "For procedure `{}`, encountered type argument of type {} which does not meet the constraint `{}`",
                     interner.lookup(callee_proc_name),
                     g_arg.e_type.as_roland_type_info_notv(interner, udt, procedures),
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

fn check_type_declared_vs_actual(
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
   if declared_type != actual_type && !actual_type.is_or_contains_or_points_to_error() && !actual_type.is_never() {
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

pub fn map_generic_to_concrete_cow<'a>(
   param_type: &'a ExpressionType,
   generic_args: &[ExpressionType],
   generic_parameters: &IndexMap<StrId, IndexSet<StrId>>,
) -> Cow<'a, ExpressionType> {
   if generic_args.is_empty() {
      Cow::Borrowed(param_type)
   } else {
      let mut new = param_type.clone();
      map_generic_to_concrete(&mut new, generic_args, generic_parameters);
      Cow::Owned(new)
   }
}

pub fn map_generic_to_concrete(
   param_type: &mut ExpressionType,
   generic_args: &[ExpressionType],
   generic_parameters: &IndexMap<StrId, IndexSet<StrId>>,
) {
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
      ExpressionType::GenericParam(x) => {
         let generic_param_index = generic_parameters.get_index_of(x).unwrap();
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
   };

   // Populate variable resolution with globals
   for gi in validation_context.global_info.iter() {
      validation_context.owned.variable_types.insert(
         gi.1.name,
         VariableDetails {
            var_type: gi.1.expr_type.e_type.clone(),
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
      try_set_inferred_type(
         &p_global.expr_type.e_type,
         p_global.initializer.unwrap(),
         validation_context.owned,
         &mut validation_context.ast.expressions,
      );

      let p_static_expr = &validation_context.ast.expressions[p_global.initializer.unwrap()];

      check_type_declared_vs_actual(
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
