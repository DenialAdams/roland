use super::type_inference::try_set_inferred_type;
use super::{StructInfo, ValidationContext, VariableDetails, VariableKind};
use crate::disjoint_set::DisjointSet;
use crate::error_handling::error_handling_macros::{
   rolandc_error, rolandc_error_no_loc, rolandc_error_w_details, rolandc_warn,
};
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{
   BinOp, BlockNode, CastType, Expression, ExpressionId, ExpressionPool, IdentifierNode, Program, Statement,
   StatementNode, UnOp,
};
use crate::semantic_analysis::EnumInfo;
use crate::size_info::{calculate_struct_size_info, sizeof_type_mem, value_type_mem_alignment};
use crate::type_data::{
   ExpressionType, IntType, IntWidth, ValueType, F32_TYPE, F64_TYPE, I32_TYPE, U32_TYPE, U64_TYPE, USIZE_TYPE,
};
use crate::typed_index_vec::Handle;
use crate::Target;
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

struct SpecialProcedure {
   name: StrId,
   required: bool,
   input_types: Vec<ExpressionType>,
   return_type: ExpressionType,
}

fn get_special_procedures(target: Target, interner: &mut Interner) -> Vec<SpecialProcedure> {
   match target {
      Target::Wasm4 => vec![
         SpecialProcedure {
            name: interner.intern("start"),
            required: false,
            input_types: vec![],
            return_type: ExpressionType::Value(ValueType::Unit),
         },
         SpecialProcedure {
            name: interner.intern("update"),
            required: true,
            input_types: vec![],
            return_type: ExpressionType::Value(ValueType::Unit),
         },
      ],
      Target::Wasi => vec![SpecialProcedure {
         name: interner.intern("main"),
         required: true,
         input_types: vec![],
         return_type: ExpressionType::Value(ValueType::Unit),
      }],
      Target::Microw8 => vec![
         SpecialProcedure {
            name: interner.intern("upd"),
            required: true,
            input_types: vec![],
            return_type: ExpressionType::Value(ValueType::Unit),
         },
         SpecialProcedure {
            name: interner.intern("snd"),
            required: false,
            input_types: vec![ExpressionType::Value(I32_TYPE)],
            return_type: ExpressionType::Value(F32_TYPE),
         },
      ],
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

fn matches(type_validation: &TypeValidator, et: &ExpressionType) -> bool {
   matches!(
      (type_validation, et),
      (TypeValidator::Any, _)
         | (TypeValidator::AnyPointer, ExpressionType::Pointer(_, _))
         | (TypeValidator::Bool, ExpressionType::Value(ValueType::Bool))
         | (
            TypeValidator::AnyInt,
            ExpressionType::Value(ValueType::Int(_) | ValueType::UnknownInt(_))
         )
         | (
            TypeValidator::AnySignedInt,
            // Accepting unknown int looks weird (could be unsigned),
            // but the trick is that we double validate this for the pertinent nodes after we've inferred types
            ExpressionType::Value(ValueType::Int(IntType { signed: true, .. }) | ValueType::UnknownInt(_))
         )
         | (
            TypeValidator::AnyFloat,
            ExpressionType::Value(ValueType::Float(_) | ValueType::UnknownFloat(_))
         )
         | (TypeValidator::AnyEnum, ExpressionType::Value(ValueType::Enum(_)))
   )
}

fn any_match(type_validations: &[TypeValidator], et: &ExpressionType) -> bool {
   let mut any_match = false;
   for type_validation in type_validations.iter() {
      any_match |= matches(type_validation, et);
   }
   any_match
}

pub fn resolve_type(
   t_type: &mut ExpressionType,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) -> Result<(), ()> {
   match t_type {
      ExpressionType::Value(vt) => resolve_value_type(vt, ei, si),
      ExpressionType::Pointer(_, vt) => resolve_value_type(vt, ei, si),
   }
}

pub fn resolve_value_type(
   v_type: &mut ValueType,
   ei: &IndexMap<StrId, EnumInfo>,
   si: &IndexMap<StrId, StructInfo>,
) -> Result<(), ()> {
   match v_type {
      ValueType::UnknownInt(_) => Ok(()),
      ValueType::UnknownFloat(_) => Ok(()),
      ValueType::Int(_) => Ok(()),
      ValueType::Float(_) => Ok(()),
      ValueType::Bool => Ok(()),
      ValueType::Unit => Ok(()),
      ValueType::Struct(_) => Ok(()),
      ValueType::Array(exp, _) => resolve_type(exp, ei, si),
      ValueType::CompileError => Ok(()),
      ValueType::Enum(_) => Ok(()),
      ValueType::Unresolved(x) => {
         if ei.contains_key(x) {
            *v_type = ValueType::Enum(*x);
            Ok(())
         } else if si.contains_key(x) {
            *v_type = ValueType::Struct(*x);
            Ok(())
         } else {
            Err(())
         }
      }
   }
}

pub fn type_and_check_validity(
   program: &mut Program,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
   expressions: &mut ExpressionPool,
   target: Target,
) {
   let mut validation_context = ValidationContext {
      target,
      string_literals: IndexSet::new(),
      variable_types: IndexMap::new(),
      procedure_info: &program.procedure_info,
      enum_info: &program.enum_info,
      struct_info: &program.struct_info,
      global_info: &program.global_info,
      cur_procedure_info: None,
      block_depth: 0,
      loop_depth: 0,
      unknown_ints: IndexSet::new(),
      unknown_floats: IndexSet::new(),
      expressions,
      struct_size_info: HashMap::new(),
      type_variables: DisjointSet::new(),
      type_variable_definitions: HashMap::new(),
      cur_procedure_locals: IndexMap::new(),
      source_to_definition: IndexMap::new(),
   };

   // Populate variable resolution with globals
   for gi in program.global_info.iter() {
      validation_context.variable_types.insert(
         *gi.0,
         VariableDetails {
            var_type: gi.1.expr_type.clone(),
            declaration_location: gi.1.location,
            kind: VariableKind::Global,
            depth: 0,
            used: true,
         },
      );
   }

   let special_procs = get_special_procedures(target, interner);
   for special_proc in special_procs.iter() {
      let actual_proc = validation_context.procedure_info.get(&special_proc.name);
      if let Some(p) = actual_proc {
         if !p.named_parameters.is_empty() {
            rolandc_error!(
               err_manager,
               p.location,
               "`{}` is a special procedure for this target ({}) and is not allowed to have named parameters",
               interner.lookup(special_proc.name),
               validation_context.target,
            );
         }
         if p.parameters != special_proc.input_types {
            if special_proc.input_types.is_empty() {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and is not allowed to have parameters",
                  interner.lookup(special_proc.name),
                  validation_context.target,
               );
            } else {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and must have the following signature: ({})",
                  interner.lookup(special_proc.name),
                  validation_context.target,
                  special_proc
                     .input_types
                     .iter()
                     .map(|x| x.as_roland_type_info(interner))
                     .collect::<Vec<String>>()
                     .join(", ")
               );
            }
         }
         if p.ret_type != special_proc.return_type {
            if special_proc.return_type == ExpressionType::Value(ValueType::Unit) {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and must not return a value",
                  interner.lookup(special_proc.name),
                  validation_context.target,
               );
            } else {
               rolandc_error!(
                  err_manager,
                  p.location,
                  "`{}` is a special procedure for this target ({}) and must return {}",
                  interner.lookup(special_proc.name),
                  validation_context.target,
                  special_proc.return_type.as_roland_type_info(interner),
               );
            }
         }
      } else if special_proc.required {
         rolandc_error_no_loc!(
            err_manager,
            "A procedure with the name `{}` must be present for this target ({})",
            interner.lookup(special_proc.name),
            validation_context.target,
         );
      }
   }

   validation_context
      .struct_size_info
      .reserve(validation_context.struct_info.len());
   for s in validation_context.struct_info.iter() {
      calculate_struct_size_info(
         *s.0,
         validation_context.enum_info,
         validation_context.struct_info,
         &mut validation_context.struct_size_info,
      );
   }

   for p_const in program.consts.iter_mut() {
      // p_const.const_type is guaranteed to be resolved at this point
      type_expression(err_manager, p_const.value, &mut validation_context, interner);
      try_set_inferred_type(&p_const.const_type, p_const.value, &mut validation_context);

      let p_const_expr = &validation_context.expressions[p_const.value];

      if p_const.const_type != *p_const_expr.exp_type.as_ref().unwrap()
         && !p_const_expr.exp_type.as_ref().unwrap().is_error_type()
      {
         let actual_type_str = p_const_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
         rolandc_error_w_details!(
            err_manager,
            &[(p_const.location, "const"), (p_const_expr.location, "expression")],
            "Declared type {} of const `{}` does not match actual expression type {}",
            p_const.const_type.as_roland_type_info(interner),
            interner.lookup(p_const.name.identifier),
            actual_type_str,
         );
      }
   }

   for p_static in program.statics.iter_mut().filter(|x| x.value.is_some()) {
      // p_static.static_type is guaranteed to be resolved at this point
      type_expression(err_manager, p_static.value.unwrap(), &mut validation_context, interner);
      try_set_inferred_type(&p_static.static_type, p_static.value.unwrap(), &mut validation_context);

      let p_static_expr = &validation_context.expressions[p_static.value.unwrap()];

      if p_static.static_type != *p_static_expr.exp_type.as_ref().unwrap()
         && !p_static_expr.exp_type.as_ref().unwrap().is_error_type()
      {
         let actual_type_str = p_static_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
         rolandc_error_w_details!(
            err_manager,
            &[(p_static.location, "static"), (p_static_expr.location, "expression")],
            "Declared type {} of static `{}` does not match actual expression type {}",
            p_static.static_type.as_roland_type_info(interner),
            interner.lookup(p_static.name.identifier),
            actual_type_str,
         );
      }
   }

   for procedure in program.procedures.iter_mut() {
      validation_context.cur_procedure_info = program.procedure_info.get(&procedure.definition.name);

      for parameter in procedure.definition.parameters.iter() {
         validation_context.variable_types.insert(
            parameter.name,
            VariableDetails {
               var_type: parameter.p_type.clone(),
               depth: 1,
               used: false,
               declaration_location: parameter.location,
               kind: VariableKind::Parameter,
            },
         );
         validation_context
            .cur_procedure_locals
            .entry(parameter.name)
            .or_insert_with(HashSet::new)
            .insert(parameter.p_type.clone());
      }

      type_block(err_manager, &mut procedure.block, &mut validation_context, interner);

      std::mem::swap(&mut validation_context.cur_procedure_locals, &mut procedure.locals);

      // Ensure that the last statement is a return statement
      // (it has already been type checked, so we don't have to check that)
      match (
         &procedure.definition.ret_type,
         procedure.block.statements.last().map(|x| &x.statement),
      ) {
         (ExpressionType::Value(ValueType::Unit), _) => (),
         (_, Some(Statement::Return(_))) => (),
         (x, _) => {
            let x_str = x.as_roland_type_info(interner);
            let mut err_details = vec![(procedure.location, "procedure defined")];
            if let Some(fs) = procedure.block.statements.last() {
               err_details.push((fs.location, "actual final statement"));
            }
            rolandc_error_w_details!(
               err_manager,
               &err_details,
               "Procedure `{}` is declared to return type {} but is missing a final return statement",
               interner.lookup(procedure.definition.name),
               x_str,
            );
         }
      }
   }

   // lower type variables
   {
      for (i, e) in validation_context.expressions.values.iter_mut().enumerate() {
         let opt_tv = match e.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::UnknownInt(x)) => Some(*x),
            ExpressionType::Value(ValueType::UnknownFloat(x)) => Some(*x),
            _ => None,
         };

         if let Some(mut tv) = opt_tv {
            tv = validation_context.type_variables.find(tv);
            let the_type = validation_context.type_variable_definitions.get(&tv);
            if let Some(t) = the_type {
               e.exp_type = Some(t.clone());
               validation_context.unknown_ints.remove(&ExpressionId::new(i));
               validation_context.unknown_floats.remove(&ExpressionId::new(i));
            }
         }

         // If we instead checked this immediately, we would error on any unary negation of an unknown int
         // for instance, let x = -1; would fail to compile!
         // as an alternative, we could introduce some sort of constraint system into the type inference engine,
         // such that we could say "this type variable makes completely unkown ints signed upon unification"
         // and immediately error if we try to union it with a known unsigned type. To be honest that sounds good,
         // but I'm postponing such an improvement for the time being. --rjm June 18, 2022
         if matches!(e.expression, Expression::UnaryOperator(UnOp::Negate, _))
            && matches!(
               e.exp_type.as_ref().unwrap(),
               ExpressionType::Value(ValueType::Int(IntType { signed: false, .. }))
            )
         {
            rolandc_error!(
               err_manager,
               e.location,
               "Unsigned integers (i.e. {}) can't be negated. Hint: Should this be a signed integer?",
               e.exp_type.as_ref().unwrap().as_roland_type_info(interner),
            );
         }
      }

      for proc in program.procedures.iter_mut() {
         for lt in proc.locals.iter_mut() {
            let tvs: Vec<usize> = lt
               .1
               .drain_filter(|x| {
                  matches!(
                     x,
                     ExpressionType::Value(ValueType::UnknownInt(_) | ValueType::UnknownFloat(_))
                  )
               })
               .map(|x| match x {
                  ExpressionType::Value(ValueType::UnknownInt(x)) => x,
                  ExpressionType::Value(ValueType::UnknownFloat(x)) => x,
                  _ => unreachable!(),
               })
               .map(|x| validation_context.type_variables.find(x))
               .collect();

            for t in tvs
               .iter()
               .flat_map(|x| validation_context.type_variable_definitions.get(x))
            {
               lt.1.insert(t.clone());
            }
         }
      }
   }

   if err_manager.errors.is_empty() {
      error_on_unknown_literals(err_manager, &mut validation_context);
   }

   program.literals = validation_context.string_literals;
   program.struct_size_info = validation_context.struct_size_info;
   program.source_to_definition = validation_context.source_to_definition;
}

fn type_statement(
   err_manager: &mut ErrorManager,
   statement: &mut StatementNode,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) {
   match &mut statement.statement {
      Statement::Assignment(lhs, rhs) => {
         type_expression(err_manager, *lhs, validation_context, interner);
         type_expression(err_manager, *rhs, validation_context, interner);

         try_set_inferred_type(
            &validation_context.expressions[*lhs].exp_type.clone().unwrap(),
            *rhs,
            validation_context,
         );

         let len = &validation_context.expressions[*lhs];
         let en = &validation_context.expressions[*rhs];

         let lhs_type = len.exp_type.as_ref().unwrap();
         let rhs_type = en.exp_type.as_ref().unwrap();

         if lhs_type.is_error_type() || rhs_type.is_error_type() {
            // avoid cascading errors
         } else if lhs_type != rhs_type {
            rolandc_error_w_details!(
               err_manager,
               &[(len.location, "left hand side"), (en.location, "right hand side")],
               "Left hand side of assignment has type {} which does not match the type of the right hand side {}",
               lhs_type.as_roland_type_info(interner),
               rhs_type.as_roland_type_info(interner),
            );
         } else if !len
            .expression
            .is_lvalue(validation_context.expressions, validation_context.global_info)
         {
            if len
               .expression
               .is_lvalue_disregard_consts(validation_context.expressions)
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
         type_block(err_manager, bn, validation_context, interner);
      }
      Statement::Continue => {
         if validation_context.loop_depth == 0 {
            rolandc_error!(
               err_manager,
               statement.location,
               "Continue statement can only be used in a loop"
            );
         }
      }
      Statement::Break => {
         if validation_context.loop_depth == 0 {
            rolandc_error!(
               err_manager,
               statement.location,
               "Break statement can only be used in a loop"
            );
         }
      }
      Statement::For(var, start, end, bn, inclusive) => {
         type_expression(err_manager, *start, validation_context, interner);
         type_expression(err_manager, *end, validation_context, interner);

         try_set_inferred_type(
            &validation_context.expressions[*start].exp_type.clone().unwrap(),
            *end,
            validation_context,
         );
         try_set_inferred_type(
            &validation_context.expressions[*end].exp_type.clone().unwrap(),
            *start,
            validation_context,
         );

         let start_expr = &validation_context.expressions[*start];
         let end_expr = &validation_context.expressions[*end];

         let result_type = match (
            start_expr.exp_type.as_ref().unwrap(),
            end_expr.exp_type.as_ref().unwrap(),
         ) {
            (lhs, _) if lhs.is_error_type() => ExpressionType::Value(ValueType::CompileError),
            (_, rhs) if rhs.is_error_type() => ExpressionType::Value(ValueType::CompileError),
            (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) if x == y => {
               ExpressionType::Value(ValueType::Int(*x))
            }
            (ExpressionType::Value(ValueType::UnknownInt(x)), ExpressionType::Value(ValueType::UnknownInt(y))) => {
               debug_assert!(x == y);
               ExpressionType::Value(ValueType::UnknownInt(*x))
            }
            _ => {
               rolandc_error_w_details!(
                  err_manager,
                  &[
                     (start_expr.location, "start of range"),
                     (end_expr.location, "end of range")
                  ],
                  "Start and end of range must be integer types of the same kind; got types `{}` and `{}`",
                  start_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
                  end_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
               );
               ExpressionType::Value(ValueType::CompileError)
            }
         };

         if *inclusive {
            rolandc_error!(
               err_manager,
               statement.location,
               "Inclusive ranges are not currently supported."
            );
         }

         // This way the variable is declared at the depth that we'll be typing in
         validation_context.block_depth += 1;
         declare_variable(err_manager, var, result_type, validation_context, interner);
         validation_context.block_depth -= 1;

         validation_context.loop_depth += 1;
         type_block(err_manager, bn, validation_context, interner);
         validation_context.loop_depth -= 1;
      }
      Statement::Loop(bn) => {
         validation_context.loop_depth += 1;
         type_block(err_manager, bn, validation_context, interner);
         validation_context.loop_depth -= 1;
      }
      Statement::Expression(en) => {
         type_expression(err_manager, *en, validation_context, interner);
      }
      Statement::IfElse(en, block_1, block_2) => {
         type_block(err_manager, block_1, validation_context, interner);
         type_statement(err_manager, block_2, validation_context, interner);
         type_expression(err_manager, *en, validation_context, interner);

         let en = &validation_context.expressions[*en];
         let if_exp_type = en.exp_type.as_ref().unwrap();
         if if_exp_type != &ExpressionType::Value(ValueType::Bool) && !if_exp_type.is_error_type() {
            rolandc_error!(
               err_manager,
               en.location,
               "Value of if expression must be a bool; got {}",
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            );
         }
      }
      Statement::Return(en) => {
         type_expression(err_manager, *en, validation_context, interner);
         let cur_procedure_info = validation_context.cur_procedure_info.unwrap();

         // Type Inference
         try_set_inferred_type(&cur_procedure_info.ret_type, *en, validation_context);

         let en = &validation_context.expressions[*en];

         if !en.exp_type.as_ref().unwrap().is_error_type()
            && en.exp_type.as_ref().unwrap() != &cur_procedure_info.ret_type
         {
            rolandc_error!(
               err_manager,
               en.location,
               "Value of return statement must match declared return type {}; got {}",
               cur_procedure_info.ret_type.as_roland_type_info(interner),
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            );
         }
      }
      Statement::VariableDeclaration(id, en, dt) => {
         type_expression(err_manager, *en, validation_context, interner);

         if let Some(v) = dt.as_mut() {
            // Failure to resolve is handled below
            let _ = resolve_type(v, validation_context.enum_info, validation_context.struct_info);
            try_set_inferred_type(v, *en, validation_context);
         }

         let en = &validation_context.expressions[*en];

         let result_type = if dt.is_some() && *dt != en.exp_type && !en.exp_type.as_ref().unwrap().is_error_type() {
            rolandc_error_w_details!(
               err_manager,
               &[(statement.location, "declaration"), (en.location, "expression")],
               "Declared type {} does not match actual expression type {}",
               dt.as_ref().unwrap().as_roland_type_info(interner),
               en.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if dt
            .as_ref()
            .map_or(false, |x| matches!(x, ExpressionType::Value(ValueType::Unresolved(_))))
         {
            let dt_str = dt.as_ref().unwrap().as_roland_type_info(interner);
            rolandc_error_w_details!(
               err_manager,
               &[(statement.location, "declaration")],
               "Variable `{}` is declared with undefined type `{}`",
               interner.lookup(id.identifier),
               dt_str,
            );
            ExpressionType::Value(ValueType::CompileError)
         } else {
            en.exp_type.clone().unwrap()
         };

         declare_variable(err_manager, id, result_type, validation_context, interner);
      }
   }
}

fn declare_variable(
   err_manager: &mut ErrorManager,
   id: &IdentifierNode,
   var_type: ExpressionType,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) {
   if validation_context.variable_types.contains_key(&id.identifier) {
      rolandc_error_w_details!(
         err_manager,
         &[(id.location, "declaration")],
         "Variable shadowing is not supported at this time (`{}`)",
         interner.lookup(id.identifier)
      );
   } else {
      validation_context.variable_types.insert(
         id.identifier,
         VariableDetails {
            var_type: var_type.clone(),
            depth: validation_context.block_depth,
            declaration_location: id.location,
            used: false,
            kind: VariableKind::Local,
         },
      );
      validation_context
         .cur_procedure_locals
         .entry(id.identifier)
         .or_insert_with(HashSet::new)
         .insert(var_type);
   }
}

fn type_block(
   err_manager: &mut ErrorManager,
   bn: &mut BlockNode,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) {
   validation_context.block_depth += 1;

   for statement in bn.statements.iter_mut() {
      type_statement(err_manager, statement, validation_context, interner);
   }

   validation_context.block_depth -= 1;

   validation_context.variable_types.retain(|k, v| {
      if v.depth <= validation_context.block_depth {
         return true;
      }

      if !v.used {
         let begin = match v.kind {
            VariableKind::Parameter => "Parameter",
            VariableKind::Local => "Local variable",
            VariableKind::Global => "Global variable",
         };
         rolandc_warn!(
            err_manager,
            v.declaration_location,
            "{} `{}` is unused",
            begin,
            interner.lookup(*k),
         );
      }

      false
   });
}

fn get_type(
   err_manager: &mut ErrorManager,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) -> ExpressionType {
   let expr_location = validation_context.expressions[expr_index].location;

   // SAFETY: it's paramount that this pointer stays valid, so we can't let the expression array resize
   // while this pointer is alive. We don't do this, because we update this expression in place and don't
   // add new expressions during validation.
   let expr_node = std::ptr::addr_of_mut!(validation_context.expressions[expr_index]);

   match unsafe { &mut (*expr_node).expression } {
      Expression::UnitLiteral => ExpressionType::Value(ValueType::Unit),
      Expression::BoolLiteral(_) => ExpressionType::Value(ValueType::Bool),
      Expression::IntLiteral { .. } => {
         validation_context.unknown_ints.insert(expr_index);
         let new_type_variable = validation_context.type_variables.add_new_set();
         ExpressionType::Value(ValueType::UnknownInt(new_type_variable))
      }
      Expression::FloatLiteral(_) => {
         validation_context.unknown_floats.insert(expr_index);
         let new_type_variable = validation_context.type_variables.add_new_set();
         ExpressionType::Value(ValueType::UnknownFloat(new_type_variable))
      }
      Expression::StringLiteral(lit) => {
         validation_context.string_literals.insert(*lit);
         ExpressionType::Value(ValueType::Struct(interner.intern("String")))
      }
      Expression::Cast {
         cast_type,
         target_type,
         expr: expr_id,
      } => {
         type_expression(err_manager, *expr_id, validation_context, interner);

         if resolve_type(
            target_type,
            validation_context.enum_info,
            validation_context.struct_info,
         )
         .is_err()
         {
            rolandc_error!(
               err_manager,
               expr_location,
               "Undeclared type `{}`",
               target_type.as_roland_type_info(interner),
            );

            return ExpressionType::Value(ValueType::CompileError);
         }

         if *cast_type == CastType::Transmute && target_type.is_pointer() {
            try_set_inferred_type(&ExpressionType::Value(USIZE_TYPE), *expr_id, validation_context);
         } else if *cast_type == CastType::Transmute && matches!(target_type, ExpressionType::Value(F64_TYPE)) {
            try_set_inferred_type(&ExpressionType::Value(U64_TYPE), *expr_id, validation_context);
         } else if *cast_type == CastType::Transmute && matches!(target_type, ExpressionType::Value(F32_TYPE)) {
            try_set_inferred_type(&ExpressionType::Value(U32_TYPE), *expr_id, validation_context);
         }

         let e = &validation_context.expressions[*expr_id];
         let e_type = e.exp_type.as_ref().unwrap();

         if e_type.is_error_type() {
            // Avoid cascading errors
            return ExpressionType::Value(ValueType::CompileError);
         }

         match cast_type {
            CastType::Extend => {
               let valid_cast = match (e_type, &target_type) {
                  (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                     if x.width == IntWidth::Pointer =>
                  {
                     // going from unsigned -> signed is ok, but signed -> unsigned is not
                     let bad = x.signed & !y.signed;
                     (IntWidth::Pointer.as_num_bytes() <= y.width.as_num_bytes()) & !bad
                  }
                  (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                     if y.width == IntWidth::Pointer =>
                  {
                     let bad = x.signed & !y.signed;
                     (x.width.as_num_bytes() <= IntWidth::Pointer.as_num_bytes()) & !bad
                  }
                  (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                     let bad = x.signed & !y.signed;
                     (x.width.as_num_bytes() < y.width.as_num_bytes()) & !bad
                  }
                  (ExpressionType::Value(F32_TYPE), ExpressionType::Value(F64_TYPE)) => true,
                  (ExpressionType::Value(ValueType::Bool), ExpressionType::Value(ValueType::Int(_))) => true,
                  _ => false,
               };

               if valid_cast {
                  target_type.clone()
               } else {
                  rolandc_error_w_details!(
                     err_manager,
                     &[(expr_location, "extend"), (e.location, "operand")],
                     "Extend encountered an operand of type {} which can not be extended to type {}",
                     e_type.as_roland_type_info(interner),
                     target_type.as_roland_type_info(interner),
                  );
                  ExpressionType::Value(ValueType::CompileError)
               }
            }
            CastType::Truncate => {
               let valid_cast = match (e_type, &target_type) {
                  (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                     if x.width == IntWidth::Pointer =>
                  {
                     IntWidth::Pointer.as_num_bytes() >= y.width.as_num_bytes()
                  }
                  (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y)))
                     if y.width == IntWidth::Pointer =>
                  {
                     x.width.as_num_bytes() >= IntWidth::Pointer.as_num_bytes()
                  }
                  (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
                     x.width.as_num_bytes() > y.width.as_num_bytes()
                  }
                  (ExpressionType::Value(F64_TYPE), ExpressionType::Value(F32_TYPE)) => true,
                  (ExpressionType::Value(ValueType::Float(_)), ExpressionType::Value(ValueType::Int(_))) => true,
                  (ExpressionType::Value(ValueType::Int(_)), ExpressionType::Value(ValueType::Float(_))) => true,
                  _ => false,
               };

               if valid_cast {
                  target_type.clone()
               } else {
                  rolandc_error_w_details!(
                     err_manager,
                     &[(expr_location, "truncate"), (e.location, "operand")],
                     "Truncate encountered an operand of type {} which can not be truncated to type {}",
                     e_type.as_roland_type_info(interner),
                     target_type.as_roland_type_info(interner),
                  );
                  ExpressionType::Value(ValueType::CompileError)
               }
            }
            CastType::Transmute => {
               if !e_type.is_concrete_type() {
                  rolandc_error_w_details!(
                     err_manager,
                     &[(expr_location, "transmute"), (e.location, "operand")],
                     "Transmute encountered an operand whose size is not yet known",
                  );
                  return ExpressionType::Value(ValueType::CompileError);
               }

               let size_source = sizeof_type_mem(
                  e_type,
                  validation_context.enum_info,
                  &validation_context.struct_size_info,
               );
               let size_target = sizeof_type_mem(
                  target_type,
                  validation_context.enum_info,
                  &validation_context.struct_size_info,
               );

               if target_type.is_enum() || e_type.is_enum() {
                  rolandc_error_w_details!(
                     err_manager,
                     &[(expr_location, "transmute"), (e.location, "operand")],
                     "Transmuting to or from enum types isn't currently supported due to the unspecified size of enums",
                  );
                  ExpressionType::Value(ValueType::CompileError)
               } else if size_source == size_target {
                  let alignment_source = value_type_mem_alignment(
                     e_type.get_value_type_or_value_being_pointed_to(),
                     validation_context.enum_info,
                     &validation_context.struct_size_info,
                  );
                  let alignment_target = value_type_mem_alignment(
                     target_type.get_value_type_or_value_being_pointed_to(),
                     validation_context.enum_info,
                     &validation_context.struct_size_info,
                  );

                  let alignment_error =
                     e_type.is_pointer() && target_type.is_pointer() && (alignment_source < alignment_target);

                  if alignment_error {
                     rolandc_error_w_details!(
                        err_manager,
                        &[(expr_location, "transmute"), (e.location, "operand")],
                        "Transmute encountered an operand of type {}, which can't be transmuted to type {} as the alignment requirements would not be met ({} vs {})",
                        e_type.as_roland_type_info(interner),
                        target_type.as_roland_type_info(interner),
                        alignment_source,
                        alignment_target,
                     );
                     ExpressionType::Value(ValueType::CompileError)
                  } else {
                     target_type.clone()
                  }
               } else {
                  rolandc_error_w_details!(
                     err_manager,
                     &[(expr_location, "transmute"), (e.location, "operand")],
                     "Transmute encountered an operand of type {} which can't be transmuted to type {} as the sizes do not match ({} vs {})",
                     e_type.as_roland_type_info(interner),
                     target_type.as_roland_type_info(interner),
                     size_source,
                     size_target,
                  );
                  ExpressionType::Value(ValueType::CompileError)
               }
            }
         }
      }
      Expression::BinaryOperator { operator, lhs, rhs } => {
         type_expression(err_manager, *lhs, validation_context, interner);
         type_expression(err_manager, *rhs, validation_context, interner);

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
            &validation_context.expressions[*lhs].exp_type.clone().unwrap(),
            *rhs,
            validation_context,
         );
         try_set_inferred_type(
            &validation_context.expressions[*rhs].exp_type.clone().unwrap(),
            *lhs,
            validation_context,
         );

         let lhs_expr = &validation_context.expressions[*lhs];
         let rhs_expr = &validation_context.expressions[*rhs];

         let lhs_type = lhs_expr.exp_type.as_ref().unwrap();
         let rhs_type = rhs_expr.exp_type.as_ref().unwrap();

         if lhs_type.is_error_type() || rhs_type.is_error_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_arg_types, lhs_type) {
            rolandc_error!(
               err_manager,
               lhs_expr.location,
               "Binary operator {:?} requires LHS to have type matching {:?}; instead got {}",
               operator,
               correct_arg_types,
               lhs_type.as_roland_type_info(interner)
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_arg_types, rhs_type) {
            rolandc_error!(
               err_manager,
               rhs_expr.location,
               "Binary operator {:?} requires RHS to have type matching {:?}; instead got {}",
               operator,
               correct_arg_types,
               rhs_type.as_roland_type_info(interner)
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if lhs_type != rhs_type {
            rolandc_error_w_details!(
               err_manager,
               &[
                  (lhs_expr.location, "left hand side"),
                  (rhs_expr.location, "right hand side")
               ],
               "Binary operator {:?} requires LHS and RHS to have identical type; instead got {} and {}",
               operator,
               lhs_type.as_roland_type_info(interner),
               rhs_type.as_roland_type_info(interner)
            );
            ExpressionType::Value(ValueType::CompileError)
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
               | BinOp::LogicalOr => ExpressionType::Value(ValueType::Bool),
            }
         }
      }
      Expression::UnaryOperator(un_op, e) => {
         type_expression(err_manager, *e, validation_context, interner);

         let e = &validation_context.expressions[*e];

         let (correct_type, node_type): (&[TypeValidator], _) = match un_op {
            UnOp::Dereference => {
               let mut new_type = e.exp_type.clone().unwrap();
               // If this fails, it will be caught by the type matcher
               let _ = new_type.decrement_indirection_count();
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
               let mut new_type = e.exp_type.clone().unwrap();
               new_type.increment_indirection_count();
               (&[TypeValidator::Any], new_type)
            }
         };

         // important that we check for concreteness first:
         // an UnknownInt is not zero sized, but sizeof_type_mem asserts on it
         let is_zst = e.exp_type.as_ref().unwrap().is_concrete_type()
            && sizeof_type_mem(
               e.exp_type.as_ref().unwrap(),
               validation_context.enum_info,
               &validation_context.struct_size_info,
            ) == 0;

         if e.exp_type.as_ref().unwrap().is_error_type() {
            // Avoid cascading errors
            ExpressionType::Value(ValueType::CompileError)
         } else if !any_match(correct_type, e.exp_type.as_ref().unwrap()) {
            rolandc_error!(
               err_manager,
               e.location,
               "Expected type {:?} for expression {:?}; instead got {}",
               correct_type,
               un_op,
               e.exp_type.as_ref().unwrap().as_roland_type_info(interner)
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::AddressOf
            && !e
               .expression
               .is_lvalue(validation_context.expressions, validation_context.global_info)
         {
            if e.expression.is_lvalue_disregard_consts(validation_context.expressions) {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempting to take a pointer to a const, which can't be done as they don't reside in memory"
               );
            } else {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "A pointer can only be taken to a value that resides in memory; i.e. a variable or parameter"
               );
            }
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::AddressOf && is_zst {
            // Allowing this wouldn't cause any clear bug (as far as I know), but it just seems whack
            rolandc_error!(
               err_manager,
               expr_location,
               "Taking a pointer to a zero sized type is disallowed, as they don't reside in memory.",
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::Dereference && is_zst {
            rolandc_error!(
               err_manager,
               expr_location,
               "Dereferencing a pointer to a zero sized type is disallowed, as there is nothing to load.",
            );
            ExpressionType::Value(ValueType::CompileError)
         } else if *un_op == UnOp::AddressOf {
            if let Expression::Variable(var) = &e.expression {
               if validation_context
                  .global_info
                  .get(&var.identifier)
                  .map_or(false, |x| x.is_const)
               {
                  rolandc_error!(
                     err_manager,
                     expr_location,
                     "Attempting to take a pointer to a const, which does not have a memory location. Hint: Should `{}` be a static?",
                     interner.lookup(var.identifier),
                  );
               }
            }
            node_type
         } else {
            node_type
         }
      }
      Expression::Variable(id) => match validation_context.variable_types.get_mut(&id.identifier) {
         Some(var_info) => {
            var_info.used = true;
            validation_context
               .source_to_definition
               .insert(expr_location, var_info.declaration_location);
            var_info.var_type.clone()
         }
         None => {
            rolandc_error!(
               err_manager,
               expr_location,
               "Encountered undefined variable `{}`",
               interner.lookup(id.identifier)
            );
            ExpressionType::Value(ValueType::CompileError)
         }
      },
      Expression::ProcedureCall {
         proc_name,
         args,
         generic_args,
      } => {
         for arg in args.iter() {
            type_expression(err_manager, arg.expr, validation_context, interner);
         }

         for g_arg in generic_args.iter_mut() {
            if resolve_type(
               &mut g_arg.gtype,
               validation_context.enum_info,
               validation_context.struct_info,
            )
            .is_err()
            {
               let etype_str = g_arg.gtype.as_roland_type_info(interner);
               rolandc_error_w_details!(
                  err_manager,
                  &[(expr_location, "call")],
                  "Undeclared type `{}` given as a type argument to `{}`",
                  etype_str,
                  interner.lookup(proc_name.identifier),
               );
            }
         }

         match validation_context.procedure_info.get(&proc_name.identifier) {
            Some(procedure_info) => {
               validation_context
                  .source_to_definition
                  .insert(proc_name.location, procedure_info.location);

               // Validate that there are no non-named arguments after named arguments, then reorder the argument list
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
                     expr_location,
                     "Call to `{}` has named argument(s) which come before non-named argument(s)",
                     interner.lookup(proc_name.identifier),
                  );
               }

               if procedure_info.type_parameters != generic_args.len() {
                  rolandc_error!(
                     err_manager,
                     expr_location,
                     "In call to `{}`, mismatched arity. Expected {} type arguments but got {}",
                     interner.lookup(proc_name.identifier),
                     procedure_info.type_parameters,
                     generic_args.len()
                  );
               }

               if args_in_order && procedure_info.parameters.len() != args.len() {
                  rolandc_error!(
                     err_manager,
                     expr_location,
                     "In call to `{}`, mismatched arity. Expected {} arguments but got {}",
                     interner.lookup(proc_name.identifier),
                     procedure_info.parameters.len(),
                     args.len()
                  );
                  // We shortcircuit here, because there will likely be lots of mismatched types if an arg was forgotten
               } else if args_in_order {
                  let expected_types = procedure_info.parameters.iter();
                  for (i, (actual, expected)) in args.iter().zip(expected_types).enumerate() {
                     // These should be at the end by now, so we've checked everything we needed to
                     if actual.name.is_some() {
                        break;
                     }

                     try_set_inferred_type(expected, actual.expr, validation_context);

                     let actual_expr = &validation_context.expressions[actual.expr];
                     let actual_type = actual_expr.exp_type.as_ref().unwrap();

                     if actual_type != expected && !actual_type.is_error_type() {
                        let actual_type_str = actual_type.as_roland_type_info(interner);
                        let expected_type_str = expected.as_roland_type_info(interner);
                        rolandc_error!(
                           err_manager,
                           actual_expr.location,
                           "In call to `{}`, argument at position {} is of type {} when we expected {}",
                           interner.lookup(proc_name.identifier),
                           i,
                           actual_type_str,
                           expected_type_str,
                        );
                     }
                  }

                  for arg in args.iter().filter(|x| x.name.is_some()) {
                     let expected = procedure_info.named_parameters.get(&arg.name.unwrap());

                     if expected.is_none() {
                        rolandc_error!(
                           err_manager,
                           expr_location,
                           "In call to `{}`, encountered named argument `{}` that does not correspond to any named parameter",
                           interner.lookup(proc_name.identifier),
                           interner.lookup(arg.name.unwrap()),
                        );
                        continue;
                     }

                     let expected = expected.unwrap();

                     try_set_inferred_type(expected, arg.expr, validation_context);

                     let arg_expr = &validation_context.expressions[arg.expr];

                     let actual_type = arg_expr.exp_type.as_ref().unwrap();
                     if actual_type != expected && !actual_type.is_error_type() {
                        let actual_type_str = actual_type.as_roland_type_info(interner);
                        let expected_type_str = expected.as_roland_type_info(interner);
                        rolandc_error!(
                           err_manager,
                           expr_location,
                           "In call to `{}`, encountered argument of type {} when we expected {} for named parameter {}",
                           interner.lookup(proc_name.identifier),
                           actual_type_str,
                           expected_type_str,
                           interner.lookup(arg.name.unwrap())
                        );
                     }
                  }
               }

               procedure_info.ret_type.clone()
            }
            None => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Encountered call to undefined procedure `{}`",
                  interner.lookup(proc_name.identifier),
               );
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::StructLiteral(struct_name, fields) => {
         for field in fields.iter() {
            type_expression(err_manager, field.1, validation_context, interner);
         }

         match validation_context.struct_info.get(&struct_name.identifier) {
            Some(defined_struct) => {
               validation_context
                  .source_to_definition
                  .insert(struct_name.location, defined_struct.location);
               let defined_fields = &defined_struct.field_types;

               let mut unmatched_fields: HashSet<StrId> = defined_fields.keys().copied().collect();
               for field in fields.iter() {
                  // Extraneous field check
                  let defined_type = match defined_fields.get(&field.0) {
                     Some(x) => x,
                     None => {
                        rolandc_error_w_details!(
                           err_manager,
                           &[
                              (expr_location, "struct instantiated"),
                              (defined_struct.location, "struct defined"),
                           ],
                           "`{}` is not a known field of struct `{}`",
                           interner.lookup(field.0),
                           interner.lookup(struct_name.identifier),
                        );
                        continue;
                     }
                  };

                  // Duplicate field check
                  if !unmatched_fields.remove(&field.0) {
                     rolandc_error_w_details!(
                        err_manager,
                        &[
                           (expr_location, "struct instantiated"),
                           (defined_struct.location, "struct defined"),
                        ],
                        "`{}` is a valid field of struct `{}`, but is duplicated",
                        interner.lookup(field.0),
                        interner.lookup(struct_name.identifier),
                     );
                  }

                  try_set_inferred_type(defined_type, field.1, validation_context);

                  let field_expr = &validation_context.expressions[field.1];

                  if field_expr.exp_type.as_ref().unwrap() != defined_type
                     && !field_expr.exp_type.as_ref().unwrap().is_error_type()
                  {
                     let field_1_type_str = field_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner);
                     let defined_type_str = defined_type.as_roland_type_info(interner);
                     rolandc_error_w_details!(
                        err_manager,
                        &[
                           (field_expr.location, "field value"),
                           (defined_struct.location, "struct defined"),
                        ],
                        "For field `{}` of struct `{}`, encountered value of type {} when we expected {}",
                        interner.lookup(field.0),
                        interner.lookup(struct_name.identifier),
                        field_1_type_str,
                        defined_type_str,
                     );
                  }
               }

               // Missing field check
               if !unmatched_fields.is_empty() {
                  let unmatched_fields_str: Vec<&str> = unmatched_fields.iter().map(|x| interner.lookup(*x)).collect();
                  rolandc_error_w_details!(
                     err_manager,
                     &[
                        (expr_location, "struct instantiated"),
                        (defined_struct.location, "struct defined"),
                     ],
                     "Literal of struct `{}` is missing fields [{}]",
                     interner.lookup(struct_name.identifier),
                     unmatched_fields_str.join(", "),
                  );
               }

               ExpressionType::Value(ValueType::Struct(struct_name.identifier))
            }
            None => {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Encountered construction of undefined struct `{}`",
                  interner.lookup(struct_name.identifier)
               );
               ExpressionType::Value(ValueType::CompileError)
            }
         }
      }
      Expression::FieldAccess(fields, lhs) => {
         type_expression(err_manager, *lhs, validation_context, interner);

         let lhs = &validation_context.expressions[*lhs];
         let mut lhs_type = lhs.exp_type.as_ref().unwrap().clone();
         let mut remaining_fields = fields.as_slice();

         let length_token = interner.intern("length");

         while !remaining_fields.is_empty() {
            let field = remaining_fields[0];
            match lhs_type {
               ExpressionType::Value(ValueType::Struct(struct_name)) => {
                  let struct_fields = &validation_context.struct_info.get(&struct_name).unwrap().field_types;
                  if let Some(new_t) = struct_fields.get(&field) {
                     lhs_type = new_t.clone();
                  } else {
                     rolandc_error!(
                        err_manager,
                        expr_location,
                        "Struct `{}` does not have a field `{}`",
                        interner.lookup(struct_name),
                        interner.lookup(field),
                     );
                     lhs_type = ExpressionType::Value(ValueType::CompileError);
                  }
               }
               ExpressionType::Value(ValueType::Array(_, _)) => {
                  if field == length_token {
                     lhs_type = ExpressionType::Value(USIZE_TYPE);
                  } else {
                     rolandc_error!(
                        err_manager,
                        expr_location,
                        "Array does not have a field `{}`. Hint: Array types have a single field `length`",
                        interner.lookup(*fields.first().unwrap()),
                     );
                     lhs_type = ExpressionType::Value(ValueType::CompileError);
                  }
               }
               ExpressionType::Value(ValueType::CompileError) => {
                  lhs_type = ExpressionType::Value(ValueType::CompileError);
               }
               other_type => {
                  rolandc_error!(
                     err_manager,
                     expr_location,
                     "Encountered field access on type {}; only structs and arrays have fields",
                     other_type.as_roland_type_info(interner)
                  );
                  lhs_type = ExpressionType::Value(ValueType::CompileError);
               }
            }
            remaining_fields = if remaining_fields.is_empty() {
               &[]
            } else {
               &remaining_fields[1..]
            };
         }
         lhs_type
      }
      Expression::ArrayLiteral(elems) => {
         for elem in elems.iter() {
            type_expression(err_manager, *elem, validation_context, interner);
         }

         let mut any_error = false;

         for i in 1..elems.len() {
            try_set_inferred_type(
               &validation_context.expressions[elems[i - 1]].exp_type.clone().unwrap(),
               elems[i],
               validation_context,
            );

            let last_elem_expr = &validation_context.expressions[elems[i - 1]];
            let this_elem_expr = &validation_context.expressions[elems[i]];

            if last_elem_expr.exp_type.as_ref().unwrap().is_error_type()
               || this_elem_expr.exp_type.as_ref().unwrap().is_error_type()
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
                  last_elem_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
                  i,
                  this_elem_expr.exp_type.as_ref().unwrap().as_roland_type_info(interner),
               );
               any_error = true;
            }
         }

         // @FixedPointerWidth
         if elems.len() > std::u32::MAX as usize {
            any_error = true;
            rolandc_error!(
               err_manager,
               expr_location,
               "Array literal has {} elements, which is more than the maximum {} elements",
               elems.len(),
               // FixedPointerWidth
               std::u32::MAX,
            );
         }

         if any_error {
            ExpressionType::Value(ValueType::CompileError)
         } else if elems.is_empty() {
            ExpressionType::Value(ValueType::Array(Box::new(ExpressionType::Value(ValueType::Unit)), 0))
         } else {
            let a_type = validation_context.expressions[elems[0]].exp_type.clone().unwrap();
            let t_len = elems.len().try_into().unwrap(); // unwrap should always succeed due to error check above
            ExpressionType::Value(ValueType::Array(Box::new(a_type), t_len))
         }
      }
      Expression::ArrayIndex { array, index } => {
         type_expression(err_manager, *array, validation_context, interner);
         type_expression(err_manager, *index, validation_context, interner);

         try_set_inferred_type(&ExpressionType::Value(USIZE_TYPE), *index, validation_context);

         let array_expression = &validation_context.expressions[*array];
         let index_expression = &validation_context.expressions[*index];

         if index_expression.exp_type.as_ref().unwrap().is_error_type() {
            // avoid cascading errors
         } else if index_expression.exp_type.as_ref().unwrap() != &ExpressionType::Value(USIZE_TYPE) {
            rolandc_error_w_details!(
               err_manager,
               &[(index_expression.location, "index")],
               "Attempted to index an array with a value of type {}, which is not usize",
               index_expression
                  .exp_type
                  .as_ref()
                  .unwrap()
                  .as_roland_type_info(interner),
            );
         }

         match &array_expression.exp_type {
            Some(x) if x.is_error_type() => ExpressionType::Value(ValueType::CompileError),
            Some(ExpressionType::Value(ValueType::Array(b, _))) => b.deref().clone(),
            Some(x @ ExpressionType::Pointer(1, ValueType::Array(_, _))) => {
               rolandc_error_w_details!(
                  err_manager,
                  &[
                     (array_expression.location, "expression"),
                     (index_expression.location, "index")
                  ],
                  "Attempted to index expression of type {}, which is not an array type. Hint: Dereference this pointer with ~",
                  x.as_roland_type_info(interner),
               );

               ExpressionType::Value(ValueType::CompileError)
            }
            Some(x) => {
               rolandc_error_w_details!(
                  err_manager,
                  &[
                     (array_expression.location, "expression"),
                     (index_expression.location, "index")
                  ],
                  "Attempted to index expression of type {}, which is not an array type",
                  x.as_roland_type_info(interner),
               );

               ExpressionType::Value(ValueType::CompileError)
            }
            None => unreachable!(),
         }
      }
      Expression::EnumLiteral(x, v) => {
         if let Some(enum_info) = validation_context.enum_info.get(&x.identifier) {
            validation_context
               .source_to_definition
               .insert(x.location, enum_info.location);
            if let Some(variant_location) = enum_info.variants.get(&v.identifier) {
               validation_context
                  .source_to_definition
                  .insert(v.location, *variant_location);
               ExpressionType::Value(ValueType::Enum(x.identifier))
            } else {
               rolandc_error!(
                  err_manager,
                  expr_location,
                  "Attempted to instantiate unknown variant `{}` of enum `{}`",
                  interner.lookup(v.identifier),
                  interner.lookup(x.identifier),
               );

               ExpressionType::Value(ValueType::CompileError)
            }
         } else {
            rolandc_error!(
               err_manager,
               expr_location,
               "Attempted to instantiate enum `{}`, which does not exist",
               interner.lookup(x.identifier),
            );

            ExpressionType::Value(ValueType::CompileError)
         }
      }
   }
}

fn type_expression(
   err_manager: &mut ErrorManager,
   expr_index: ExpressionId,
   validation_context: &mut ValidationContext,
   interner: &mut Interner,
) {
   validation_context.expressions[expr_index].exp_type =
      Some(get_type(err_manager, expr_index, validation_context, interner));
}

fn error_on_unknown_literals(err_manager: &mut ErrorManager, validation_context: &mut ValidationContext) {
   if !validation_context.unknown_ints.is_empty() {
      let err_details: Vec<_> = validation_context
         .unknown_ints
         .iter()
         .map(|x| {
            let loc = validation_context.expressions[*x].location;
            (loc, "int literal")
         })
         .collect();
      rolandc_error_w_details!(
         err_manager,
         &err_details,
         "We weren't able to determine the types of {} int literals",
         validation_context.unknown_ints.len()
      );
   }

   if !validation_context.unknown_floats.is_empty() {
      let err_details: Vec<_> = validation_context
         .unknown_floats
         .iter()
         .map(|x| {
            let loc = validation_context.expressions[*x].location;
            (loc, "float literal")
         })
         .collect();
      rolandc_error_w_details!(
         err_manager,
         &err_details,
         "We weren't able to determine the types of {} float literals",
         validation_context.unknown_floats.len()
      );
   }
}
