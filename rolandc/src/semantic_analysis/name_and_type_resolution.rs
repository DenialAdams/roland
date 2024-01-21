use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use super::{ProcedureInfo, GlobalKind};
use crate::error_handling::ErrorManager;
use crate::error_handling::error_handling_macros::rolandc_error;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, BlockNode, DeclarationValue, Expression, ExpressionId, ProcImplSource, ProcedureId, Statement, StatementId,
   UserDefinedTypeId, UserDefinedTypeInfo,
};
use crate::size_info::calculate_struct_size_info;
use crate::source_info::SourceInfo;
use crate::type_data::ExpressionType;
use crate::Program;

struct ResCtx<'a> {
   proc_name_table: &'a HashMap<StrId, ProcedureId>,
   user_defined_type_name_table: &'a HashMap<StrId, UserDefinedTypeId>,
   user_defined_types: &'a mut UserDefinedTypeInfo,
   interner: &'a Interner,
   ast: &'a mut AstPool,
   cur_procedure_info: Option<&'a ProcedureInfo>,
}

pub fn resolve_names_and_types(program: &mut Program, err_manager: &mut ErrorManager, interner: &mut Interner) {
   let mut ctx = ResCtx {
      proc_name_table: &program.procedure_name_table,
      user_defined_type_name_table: &program.user_defined_type_name_table,
      user_defined_types: &mut program.user_defined_types,
      ast: &mut program.ast,
      interner,
      cur_procedure_info: None,
   };

   for (id, procedure) in program.procedures.iter_mut() {
      let ProcImplSource::Body(block) = &procedure.proc_impl else {
         continue;
      };

      ctx.cur_procedure_info = program.procedure_info.get(id);

      resolve_block(err_manager, block, &mut ctx);
   }

   for s in ctx.user_defined_types.struct_info.iter() {
      for (_, &default_expr) in s.1.default_values.iter() {
         // This is tricky.
         // 1 - cur_procedure_info is not sufficient for this. we need to resolve the expressions with the struct's generic parameters
         // 2 - resolving the type of a struct can clone and create a new struct. this new struct must have new expressions.
         // ugh. nocheckin
         todo!()
      }
   }

   for p_const in program.consts.iter_mut() {
      resolve_expression(err_manager, p_const.value, &mut ctx);
   }

   for p_static in program
      .global_info
      .values()
      .filter(|x| x.kind == GlobalKind::Static && x.initializer.is_some())
   {
      resolve_expression(err_manager, p_static.initializer.unwrap(), &mut ctx);
   }
}

fn resolve_block(err_manager: &mut ErrorManager, block: &BlockNode, ctx: &mut ResCtx) {
   for statement in block.statements.iter().copied() {
      resolve_statement(err_manager, statement, ctx);
   }
}

fn resolve_statement(err_manager: &mut ErrorManager, statement: StatementId, ctx: &mut ResCtx) {
   let mut the_statement = std::mem::replace(
      &mut ctx.ast.statements[statement].statement,
      Statement::Break,
   );
   match &mut the_statement {
      Statement::Assignment(lhs, rhs) => {
         resolve_expression(err_manager, *lhs, ctx);
         resolve_expression(err_manager, *rhs, ctx);
      }
      Statement::Block(bn) => {
         resolve_block(err_manager, bn, ctx);
      }
      Statement::Continue => (),
      Statement::Break => (),
      Statement::For {
         range_start: start,
         range_end: end,
         body: bn,
         induction_var_name: _,
         range_inclusive: _,
         induction_var: _,
      } => {
         resolve_expression(err_manager, *start, ctx);
         resolve_expression(err_manager, *end, ctx);
         resolve_block(err_manager, bn, ctx);
      }
      Statement::While(cond, bn) => {
         resolve_expression(err_manager, *cond, ctx);

         resolve_block(err_manager, bn, ctx);
      }
      Statement::Loop(bn) => {
         resolve_block(err_manager, bn, ctx);
      }
      Statement::Defer(si) => {
         resolve_statement(err_manager, *si, ctx);
      }
      Statement::Expression(en) => {
         resolve_expression(err_manager, *en, ctx);
      }
      Statement::IfElse(en, block_1, block_2) => {
         resolve_block(err_manager, block_1, ctx);
         resolve_statement(err_manager, *block_2, ctx);
         resolve_expression(err_manager, *en, ctx);
      }
      Statement::Return(en) => {
         resolve_expression(err_manager, *en, ctx);
      }
      Statement::VariableDeclaration(_, opt_enid, dt, _) => {
         if let DeclarationValue::Expr(enid) = opt_enid {
            resolve_expression(err_manager, *enid, ctx);
         }

         if let Some(v) = dt.as_mut() {
            if !resolve_type(
               &mut v.e_type,
               ctx.user_defined_type_name_table,
               ctx.cur_procedure_info.map(|x| &x.type_parameters),
               err_manager,
               ctx.interner,
               v.location,
               ctx.user_defined_types,
            ) {
               v.e_type = ExpressionType::CompileError;
            }
         };
      }
   }
   ctx.ast.statements[statement].statement = the_statement;
}

fn resolve_expression(err_manager: &mut ErrorManager, expr_index: ExpressionId, ctx: &mut ResCtx) {
   let expr_location = ctx.ast.expressions[expr_index].location;
   match &mut ctx.ast.expressions[expr_index].expression {
      Expression::Cast { target_type, .. } => {
         if !resolve_type(
            target_type,
            ctx.user_defined_type_name_table,
            ctx.cur_procedure_info.map(|x| &x.type_parameters),
            err_manager,
            ctx.interner,
            expr_location,
            ctx.user_defined_types,
         ) {
            *target_type = ExpressionType::CompileError;
         }
      }
      Expression::UnresolvedProcLiteral(name, g_args) => {
         for g_arg in g_args.iter_mut() {
            resolve_type(
               &mut g_arg.e_type,
               ctx.user_defined_type_name_table,
               ctx.cur_procedure_info.map(|x| &x.type_parameters),
               err_manager,
               ctx.interner,
               g_arg.location,
               ctx.user_defined_types,
            );
         }

         if let Some(proc_id) = ctx.proc_name_table.get(&name.str).copied() {
            ctx.ast.expressions[expr_index].expression =
               Expression::BoundFcnLiteral(proc_id, std::mem::take(g_args).into_boxed_slice());
         }
      }
      _ => (),
   }

   let the_expr = std::mem::replace(
      &mut ctx.ast.expressions[expr_index].expression,
      Expression::UnitLiteral,
   );
   match &the_expr {
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::Cast {
         expr: expr_id,
         ..
      } => {
         resolve_expression(err_manager, *expr_id, ctx);
      }
      Expression::BinaryOperator { operator: _, lhs, rhs } => {
         resolve_expression(err_manager, *lhs, ctx);
         resolve_expression(err_manager, *rhs, ctx);
      }
      Expression::UnaryOperator(_, e) => {
         resolve_expression(err_manager, *e, ctx);
      }
      Expression::BoundFcnLiteral(_, _) => (),
      Expression::UnresolvedProcLiteral(_, _) => (),
      Expression::UnresolvedVariable(_) => (),
      Expression::UnresolvedStructLiteral(_, fields) => {
         for field_val in fields.iter().flat_map(|x| x.1) {
            resolve_expression(err_manager, field_val, ctx);
         }
      }
      Expression::Variable(_) => (),
      Expression::ProcedureCall { proc_expr, args } => {
         resolve_expression(err_manager, *proc_expr, ctx);
         for arg in args.iter() {
            resolve_expression(err_manager, arg.expr, ctx);
         }
      }
      Expression::FieldAccess(_, lhs) => {
         resolve_expression(err_manager, *lhs, ctx);
      }
      Expression::ArrayLiteral(elems) => {
         for elem in elems.iter() {
            resolve_expression(err_manager, *elem, ctx);
         }
      }
      Expression::ArrayIndex { array, index } => {
         resolve_expression(err_manager, *array, ctx);
         resolve_expression(err_manager, *index, ctx);
      }
      Expression::UnresolvedEnumLiteral(_, _) => (),
      Expression::IfX(a, b, c) => {
         resolve_expression(err_manager, *a, ctx);
         resolve_expression(err_manager, *b, ctx);
         resolve_expression(err_manager, *c, ctx);
      }
      Expression::StructLiteral(_, _) | Expression::EnumLiteral(_, _) => unreachable!(),
   }
   ctx.ast.expressions[expr_index].expression = the_expr;
}

pub fn resolve_type<T>(
   v_type: &mut ExpressionType,
   type_name_table: &HashMap<StrId, UserDefinedTypeId>,
   type_params: Option<&T>,
   err_manager: &mut ErrorManager,
   interner: &Interner,
   location_for_error: SourceInfo,
   udt: &mut UserDefinedTypeInfo,
) -> bool
where
   T: CanCheckContainsStrId,
{
   match v_type {
      ExpressionType::Pointer(vt) => resolve_type(
         vt,
         type_name_table,
         type_params,
         err_manager,
         interner,
         location_for_error,
         udt,
      ),
      ExpressionType::Never => true,
      ExpressionType::Unknown(_) => true,
      ExpressionType::Int(_) => true,
      ExpressionType::Float(_) => true,
      ExpressionType::Bool => true,
      ExpressionType::Unit => true,
      ExpressionType::Struct(_) => true,
      ExpressionType::Union(_) => true,
      ExpressionType::Array(exp, _) => resolve_type(
         exp,
         type_name_table,
         type_params,
         err_manager,
         interner,
         location_for_error,
         udt,
      ),
      ExpressionType::CompileError => true,
      ExpressionType::Enum(_) => true,
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
               err_manager,
               interner,
               location_for_error,
               udt,
            );
         }
         resolve_result &= resolve_type(
            ret_val,
            type_name_table,
            type_params,
            err_manager,
            interner,
            location_for_error,
            udt,
         );
         resolve_result
      }
      ExpressionType::GenericParam(_) => true,
      ExpressionType::ProcedureItem(_, _) => true, // This type contains other types, but this type itself can never be written down. It should always be valid
      ExpressionType::Unresolved { name: x, generic_args } => {
         let mut args_ok = true;
         for g_arg in generic_args.iter_mut() {
            args_ok &= resolve_type(
               g_arg,
               type_name_table,
               type_params,
               err_manager,
               interner,
               location_for_error,
               udt,
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
            Some(UserDefinedTypeId::Struct(y)) => {
               if !generic_args.is_empty() {
                  let si: &super::StructInfo = &udt.struct_info[*y];
                  if generic_args.len() != si.type_parameters.len() {
                     rolandc_error!(
                        err_manager,
                        location_for_error,
                        "Mismatched arity for struct '{}'. Expected {} type arguments but got {}",
                        interner.lookup(*x),
                        si.type_parameters.len(),
                        generic_args.len(),
                     );
                     return false;
                  }
                  let mut new_si = si.clone();
                  new_si.type_parameters.clear();
                  for ft in new_si.field_types.iter_mut() {
                     // nocheckin - this is obviously wrong. what about &T etc?
                     // need to use map_generic_to_concrete
                     // (and rename it lol, since we can be mapping from generic struct param -> generic proc param)
                     if let ExpressionType::GenericParam(n) = ft.1.e_type {
                        ft.1.e_type = generic_args[si.type_parameters.get_index_of(&n).unwrap()].clone();
                     }
                  }
                  for dv in new_si.default_values.iter_mut() {
                     // nocheckin
                     // We must clone the default value and map any usage of old T to new T
                     // This is complicated by the fact that default values have likely not yet been resolved
                     unimplemented!();
                  }
                  let new_id = udt.struct_info.insert(new_si);
                  calculate_struct_size_info(new_id, udt);
                  ExpressionType::Struct(new_id)
               } else {
                  ExpressionType::Struct(*y)
               }
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
               } else if type_params.map_or(false, |tp| tp.contains(x)) {
                  if !generic_args.is_empty() {
                     rolandc_error!(
                        err_manager,
                        location_for_error,
                        "Type arguments are not supported for type parameters",
                     );

                     return false;
                  }
                  ExpressionType::GenericParam(*x)
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

pub trait CanCheckContainsStrId {
   fn contains(&self, x: &StrId) -> bool;
}

impl<V> CanCheckContainsStrId for IndexMap<StrId, V> {
   fn contains(&self, x: &StrId) -> bool {
      self.contains_key(x)
   }
}

impl CanCheckContainsStrId for IndexSet<StrId> {
   fn contains(&self, x: &StrId) -> bool {
      self.contains(x)
   }
}

impl CanCheckContainsStrId for () {
   fn contains(&self, _: &StrId) -> bool {
      return false;
   }
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