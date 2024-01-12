use slotmap::SlotMap;

use crate::interner::Interner;
use crate::parse::{ArgumentNode, BinOp, EnumId, Expression, ExpressionId, ExpressionNode, Program, UnOp};
use crate::semantic_analysis::EnumInfo;
use crate::source_info::SourceInfo;
use crate::type_data::{ExpressionType, IntWidth, F32_TYPE, F64_TYPE, I16_TYPE, I8_TYPE, USIZE_TYPE};

fn lower_type(the_type: &mut ExpressionType, enum_info: &SlotMap<EnumId, EnumInfo>) {
   match the_type {
      ExpressionType::Enum(a) => {
         *the_type = enum_info.get(*a).unwrap().base_type.clone();
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

fn lower_single_expression(expression_node: &mut ExpressionNode, enum_info: &SlotMap<EnumId, EnumInfo>) {
   match &mut expression_node.expression {
      Expression::EnumLiteral(a, b) => {
         let ei = enum_info.get(*a).unwrap();
         let replacement_expr = match ei.base_type {
            ExpressionType::Unit => Expression::UnitLiteral,
            ExpressionType::Int(_) => {
               let val = ei.variants.get_index_of(b).unwrap();
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

fn replace_cast_expr(
   src: ExpressionId,
   target: &ExpressionNode,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let src_type = program.ast.expressions[src].exp_type.as_ref().unwrap();
   let target_type = target.exp_type.as_ref().unwrap();
   let proc_name = match (src_type, target_type) {
      (&F32_TYPE, &I8_TYPE) => "f32_to_i8",
      (&F64_TYPE, &I8_TYPE) => "f64_to_i8",
      (&F32_TYPE, &I16_TYPE) => "f32_to_i16",
      (&F64_TYPE, &I16_TYPE) => "f64_to_i16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location: target.location,
   })
}

fn replace_negate(
   operand: ExpressionId,
   location: SourceInfo,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let operand_type = program.ast.expressions[operand].exp_type.as_ref().unwrap();
   let proc_name = match *operand_type {
      I8_TYPE => "neg_i8",
      I16_TYPE => "neg_i16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location,
   })
}

fn replace_div(
   operand: ExpressionId,
   location: SourceInfo,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let operand_type = program.ast.expressions[operand].exp_type.as_ref().unwrap();
   let proc_name = match *operand_type {
      I8_TYPE => "div_i8",
      I16_TYPE => "div_i16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location,
   })
}

fn replace_mod(
   operand: ExpressionId,
   location: SourceInfo,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let operand_type = program.ast.expressions[operand].exp_type.as_ref().unwrap();
   let proc_name = match *operand_type {
      I8_TYPE => "mod_i8",
      I16_TYPE => "mod_i16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location,
   })
}

pub fn replace_nonnative_casts_and_unique_overflow(program: &mut Program, interner: &Interner) {
   let mut replacements = vec![];
   for (expression, v) in program.ast.expressions.iter() {
      let opt_new_expr = match v.expression {
         Expression::Cast { expr: src_expr, .. } => replace_cast_expr(src_expr, v, program, interner),
         Expression::UnaryOperator(UnOp::Negate, inner_expr) => {
            replace_negate(inner_expr, v.location, program, interner)
         }
         Expression::BinaryOperator { operator, lhs, .. } => match operator {
            BinOp::Divide => replace_div(lhs, v.location, program, interner),
            BinOp::Remainder => replace_mod(lhs, v.location, program, interner),
            _ => None,
         },
         _ => None,
      };
      if let Some(new_expr) = opt_new_expr {
         replacements.push((expression, new_expr));
      }
   }
   for replacement in replacements {
      let pid = program.ast.expressions.insert(replacement.1);
      let args = match &program.ast.expressions[replacement.0].expression {
         Expression::Cast { expr: castee, .. } => [Some(*castee), None],
         Expression::UnaryOperator(_, operand) => [Some(*operand), None],
         Expression::BinaryOperator { lhs, rhs, .. } => [Some(*lhs), Some(*rhs)],
         _ => unreachable!(),
      };
      program.ast.expressions[replacement.0].expression = Expression::ProcedureCall {
         proc_expr: pid,
         args: args
            .iter()
            .flatten()
            .map(|x| ArgumentNode { name: None, expr: *x })
            .collect(),
      };
   }
}
