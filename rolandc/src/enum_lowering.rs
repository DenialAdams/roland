use indexmap::IndexMap;

use crate::interner::StrId;
use crate::parse::{Expression, ExpressionId, ExpressionPool, Program};
use crate::semantic_analysis::EnumInfo;
use crate::type_data::ExpressionType;
use crate::typed_index_vec::Handle;

fn lower_enum_type(the_enum_type: &mut ExpressionType, enum_info: &IndexMap<StrId, EnumInfo>) {
   match the_enum_type {
      ExpressionType::Enum(a) => {
         *the_enum_type = enum_info.get(a).unwrap().base_type.clone();
      }
      ExpressionType::Array(inner_type, _) => {
         lower_enum_type(inner_type, enum_info);
      }
      ExpressionType::Pointer(inner_type) => {
         lower_enum_type(inner_type, enum_info);
      }
      ExpressionType::ProcedurePointer { parameters, ret_type } => {
         for param in parameters.iter_mut() {
            lower_enum_type(param, enum_info);
         }
         lower_enum_type(ret_type, enum_info);
      }
      ExpressionType::ProcedureItem(_, type_params) => {
         for type_param in type_params.iter_mut() {
            lower_enum_type(type_param, enum_info)
         }
      }
      _ => (),
   }
}

fn lower_single_expression(
   expressions: &mut ExpressionPool,
   expression_id: ExpressionId,
   enum_info: &IndexMap<StrId, EnumInfo>,
) {
   match &mut expressions[expression_id].expression {
      Expression::EnumLiteral(a, b) => {
         let ei = enum_info.get(&a.str).unwrap();
         let replacement_expr = match ei.base_type {
            ExpressionType::Unit => Expression::UnitLiteral,
            ExpressionType::Int(_) => {
               let val = ei.variants.get_index_of(&b.str).unwrap();
               Expression::IntLiteral {
                  val: val as u64,
                  synthetic: true,
               }
            }
            _ => unreachable!(),
         };
         expressions[expression_id].expression = replacement_expr;
      }
      Expression::Cast {
         cast_type: _,
         target_type,
         expr: _,
      } => {
         lower_enum_type(target_type, enum_info);
      }
      Expression::BoundFcnLiteral(_, generic_args) => {
         for g_arg in generic_args.iter_mut() {
            lower_enum_type(&mut g_arg.gtype, enum_info);
         }
      }
      _ => (),
   }

   lower_enum_type(expressions[expression_id].exp_type.as_mut().unwrap(), enum_info);
}

pub fn lower_enums(program: &mut Program, expressions: &mut ExpressionPool) {
   for i in 0..expressions.len() {
      lower_single_expression(expressions, ExpressionId::new(i), &program.enum_info);
   }

   // We omit lowering the types in program.structs and program.statics,
   // as they should no longer be read.

   for struct_info in program.struct_info.iter_mut() {
      for field_type in struct_info.1.field_types.values_mut() {
         lower_enum_type(&mut field_type.e_type, &program.enum_info);
      }
   }

   for procedure in program.procedures.iter_mut() {
      lower_enum_type(&mut procedure.definition.ret_type.e_type, &program.enum_info);
      for param in procedure.definition.parameters.iter_mut() {
         lower_enum_type(&mut param.p_type.e_type, &program.enum_info);
      }
   }

   for a_global in program.global_info.iter_mut() {
      lower_enum_type(&mut a_global.1.expr_type, &program.enum_info);
   }
}
