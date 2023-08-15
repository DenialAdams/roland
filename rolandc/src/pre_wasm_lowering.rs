use indexmap::IndexMap;

use crate::interner::{Interner, StrId};
use crate::parse::{ArgumentNode, Expression, ExpressionNode, Program};
use crate::semantic_analysis::EnumInfo;
use crate::type_data::{ExpressionType, IntWidth, F32_TYPE, F64_TYPE, I16_TYPE, I8_TYPE, USIZE_TYPE};

fn lower_type(the_type: &mut ExpressionType, enum_info: &IndexMap<StrId, EnumInfo>) {
   match the_type {
      ExpressionType::Enum(a) => {
         *the_type = enum_info.get(a).unwrap().base_type.clone();
      }
      ExpressionType::Array(inner_type, _) => {
         lower_type(inner_type, enum_info);
      }
      ExpressionType::Pointer(_) => {
         *the_type = USIZE_TYPE;
      }
      ExpressionType::Int(it) => {
         if it.width == IntWidth::Pointer {
            it.width = IntWidth::Four;
         }
      }
      ExpressionType::ProcedurePointer { parameters, ret_type } => {
         for param in parameters.iter_mut() {
            lower_type(param, enum_info);
         }
         lower_type(ret_type, enum_info);
      }
      ExpressionType::ProcedureItem(_, type_params) => {
         for type_param in type_params.iter_mut() {
            lower_type(type_param, enum_info);
         }
      }
      _ => (),
   }
}

fn lower_single_expression(expression_node: &mut ExpressionNode, enum_info: &IndexMap<StrId, EnumInfo>) {
   match &mut expression_node.expression {
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
         expression_node.expression = replacement_expr;
      }
      Expression::Cast {
         cast_type: _,
         target_type,
         expr: _,
      } => {
         lower_type(target_type, enum_info);
      }
      Expression::BoundFcnLiteral(_, generic_args) => {
         for g_arg in generic_args.iter_mut() {
            lower_type(&mut g_arg.e_type, enum_info);
         }
      }
      _ => (),
   }

   lower_type(expression_node.exp_type.as_mut().unwrap(), enum_info);
}

pub fn lower_enums_and_pointers(program: &mut Program) {
   for e in program.ast.expressions.values_mut() {
      lower_single_expression(e, &program.user_defined_types.enum_info);
   }

   for struct_info in program.user_defined_types.struct_info.iter_mut() {
      for field_type in struct_info.1.field_types.values_mut() {
         lower_type(&mut field_type.e_type, &program.user_defined_types.enum_info);
      }
   }

   for union_info in program.user_defined_types.union_info.iter_mut() {
      for field_type in union_info.1.field_types.values_mut() {
         lower_type(&mut field_type.e_type, &program.user_defined_types.enum_info);
      }
   }

   for procedure in program.procedures.values_mut() {
      lower_type(
         &mut procedure.definition.ret_type.e_type,
         &program.user_defined_types.enum_info,
      );
      for param in procedure.definition.parameters.iter_mut() {
         lower_type(&mut param.p_type.e_type, &program.user_defined_types.enum_info);
      }
      for var_type in procedure.locals.values_mut() {
         lower_type(var_type, &program.user_defined_types.enum_info);
      }
   }

   for a_global in program.global_info.iter_mut() {
      lower_type(&mut a_global.1.expr_type.e_type, &program.user_defined_types.enum_info);
   }
}

pub fn replace_nonnative_casts(program: &mut Program, interner: &Interner) {
   let mut replacements = vec![];
   for (expression, v) in program.ast.expressions.iter() {
      let target_type = v.exp_type.as_ref().unwrap();
      let Expression::Cast { expr: src_expr, .. } = &v.expression else {
         continue;
      };
      let src_type = program.ast.expressions[*src_expr].exp_type.as_ref().unwrap();
      let proc_name = match (src_type, target_type) {
         (&F32_TYPE, &I8_TYPE) => "f32_to_i8",
         (&F64_TYPE, &I8_TYPE) => "f64_to_i8",
         (&F32_TYPE, &I16_TYPE) => "f32_to_i16",
         (&F64_TYPE, &I16_TYPE) => "f64_to_i16",
         _ => continue,
      };
      let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
      let new_proc_expr = ExpressionNode {
         expression: Expression::BoundFcnLiteral(proc_id, vec![].into_boxed_slice()),
         exp_type: Some(ExpressionType::ProcedureItem(proc_id, vec![].into_boxed_slice())),
         location: v.location,
      };
      replacements.push((expression, new_proc_expr));
   }
   for replacement in replacements {
      let pid = program.ast.expressions.insert(replacement.1);
      let Expression::Cast { expr: castee, .. } = &program.ast.expressions[replacement.0].expression else {
         continue;
      };
      program.ast.expressions[replacement.0].expression = Expression::ProcedureCall {
         proc_expr: pid,
         args: vec![ArgumentNode {
            name: None,
            expr: *castee,
         }]
         .into_boxed_slice(),
      };
   }
}
