use slotmap::SlotMap;

use crate::backend::linearize::CfgInstruction;
use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::Interner;
use crate::parse::{
   ArgumentNode, BinOp, EnumId, Expression, ExpressionId, ExpressionNode, ExpressionPool, Program, UnOp,
   UserDefinedTypeInfo,
};
use crate::semantic_analysis::EnumInfo;
use crate::size_info::sizeof_type_mem;
use crate::source_info::SourceInfo;
use crate::type_data::{ExpressionType, IntType, IntWidth, F32_TYPE, F64_TYPE, I16_TYPE, I8_TYPE, U16_TYPE, U8_TYPE};
use crate::Target;

fn lower_type(the_type: &mut ExpressionType, enum_info: &SlotMap<EnumId, EnumInfo>, target: Target) {
   match the_type {
      ExpressionType::Enum(a) => {
         *the_type = enum_info.get(*a).unwrap().base_type.clone();
      }
      ExpressionType::Array(inner_type, _) => {
         lower_type(inner_type, enum_info, target);
      }
      ExpressionType::Pointer(_) => {
         *the_type = ExpressionType::Int(IntType {
            width: target.lowered_ptr_width(),
            signed: false,
         });
      }
      ExpressionType::Int(it) => {
         if it.width == IntWidth::Pointer {
            it.width = target.lowered_ptr_width();
         }
      }
      ExpressionType::ProcedurePointer { parameters, ret_type } => {
         for param in parameters.iter_mut() {
            lower_type(param, enum_info, target);
         }
         lower_type(ret_type, enum_info, target);
      }
      ExpressionType::ProcedureItem(_, type_params) => {
         for type_param in type_params.iter_mut() {
            lower_type(type_param, enum_info, target);
         }
      }
      _ => (),
   }
}

fn lower_single_expression(e: ExpressionId, udt: &UserDefinedTypeInfo, target: Target, ast: &mut ExpressionPool) {
   match &mut ast[e].expression {
      Expression::EnumLiteral(a, b) => {
         let ei = udt.enum_info.get(*a).unwrap();
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
         ast[e].expression = replacement_expr;
      }
      Expression::Cast {
         cast_type: _,
         target_type,
         expr: _,
      } => {
         lower_type(target_type, &udt.enum_info, target);
      }
      Expression::BoundFcnLiteral(_, generic_args) => {
         for g_arg in generic_args.iter_mut() {
            lower_type(&mut g_arg.e_type, &udt.enum_info, target);
         }
      }
      _ => (),
   }
}

pub fn lower_aggregate_access(program: &mut Program, target: Target) {
   let expression_ids: Vec<ExpressionId> = program.ast.expressions.keys().collect();
   for e in expression_ids {
      match &program.ast.expressions[e].expression {
         Expression::FieldAccess(f, base) => {
            let f = *f;
            let base = *base;
            let mem_offset = match program.ast.expressions[base]
               .exp_type
               .as_ref()
               .unwrap()
               .get_type_or_type_being_pointed_to()
            {
               ExpressionType::Struct(s, _) => program
                  .user_defined_types
                  .struct_info
                  .get(*s)
                  .unwrap()
                  .size
                  .as_ref()
                  .unwrap()
                  .field_offsets_mem
                  .get(&f)
                  .copied()
                  .unwrap(),
               ExpressionType::Union(_, _) => 0,
               _ => unreachable!(),
            };
            if mem_offset == 0 {
               program.ast.expressions[e].expression = program.ast.expressions[base].expression.clone();
            } else {
               let offset_node = program.ast.expressions.insert(ExpressionNode {
                  exp_type: Some(ExpressionType::Int(IntType {
                     signed: false,
                     width: IntWidth::Pointer,
                  })),
                  expression: Expression::IntLiteral {
                     val: u64::from(mem_offset),
                     synthetic: true,
                  },
                  location: program.ast.expressions[e].location,
               });
               program.ast.expressions[e].expression = Expression::BinaryOperator {
                  operator: BinOp::Add,
                  lhs: base,
                  rhs: offset_node,
               };
            }
         }
         Expression::ArrayIndex { array, index } => {
            let array = *array;
            let index = *index;
            let sizeof_inner = match program.ast.expressions[array]
               .exp_type
               .as_ref()
               .unwrap()
               .get_type_or_type_being_pointed_to()
            {
               ExpressionType::Array(x, _) => sizeof_type_mem(x, &program.user_defined_types, target),
               _ => unreachable!(),
            };
            let sizeof_literal_node = program.ast.expressions.insert(ExpressionNode {
               exp_type: Some(ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Pointer,
               })),
               expression: Expression::IntLiteral {
                  val: u64::from(sizeof_inner),
                  synthetic: true,
               },
               location: program.ast.expressions[e].location,
            });
            let mul_node = program.ast.expressions.insert(ExpressionNode {
               exp_type: Some(ExpressionType::Int(IntType {
                  signed: false,
                  width: target.lowered_ptr_width(),
               })),
               expression: Expression::BinaryOperator {
                  operator: BinOp::Multiply,
                  lhs: sizeof_literal_node,
                  rhs: index,
               },
               location: program.ast.expressions[e].location,
            });
            program.ast.expressions[e].expression = Expression::BinaryOperator {
               operator: BinOp::Add,
               lhs: array,
               rhs: mul_node,
            };
         }
         _ => continue,
      }
   }
}

pub fn lower_enums_and_pointers(program: &mut Program, target: Target) {
   let expression_ids: Vec<ExpressionId> = program.ast.expressions.keys().collect();
   for e in expression_ids {
      lower_single_expression(e, &program.user_defined_types, target, &mut program.ast.expressions);
   }

   for e in program.ast.expressions.values_mut() {
      lower_type(
         e.exp_type.as_mut().unwrap(),
         &program.user_defined_types.enum_info,
         target,
      );
   }

   for struct_info in program.user_defined_types.struct_info.values_mut() {
      for field_type in struct_info.field_types.values_mut() {
         lower_type(&mut field_type.e_type, &program.user_defined_types.enum_info, target);
      }
   }

   for union_info in program.user_defined_types.union_info.values_mut() {
      for field_type in union_info.field_types.values_mut() {
         lower_type(&mut field_type.e_type, &program.user_defined_types.enum_info, target);
      }
   }

   for procedure in program.procedures.values_mut() {
      lower_type(
         &mut procedure.definition.ret_type.e_type,
         &program.user_defined_types.enum_info,
         target,
      );
      for param in procedure.definition.parameters.iter_mut() {
         lower_type(&mut param.p_type.e_type, &program.user_defined_types.enum_info, target);
      }
   }

   for body in program.procedure_bodies.values_mut() {
      for var_type in body.locals.values_mut() {
         lower_type(var_type, &program.user_defined_types.enum_info, target);
      }
   }

   for a_global in program.non_stack_var_info.iter_mut() {
      lower_type(
         &mut a_global.1.expr_type.e_type,
         &program.user_defined_types.enum_info,
         target,
      );
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

fn replace_add(
   operand: ExpressionId,
   location: SourceInfo,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let operand_type = program.ast.expressions[operand].exp_type.as_ref().unwrap();
   let proc_name = match *operand_type {
      I8_TYPE => "add_i8",
      I16_TYPE => "add_i16",
      U8_TYPE => "add_u8",
      U16_TYPE => "add_u16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location,
   })
}

fn replace_sub(
   operand: ExpressionId,
   location: SourceInfo,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let operand_type = program.ast.expressions[operand].exp_type.as_ref().unwrap();
   let proc_name = match *operand_type {
      I8_TYPE => "sub_i8",
      I16_TYPE => "sub_i16",
      U8_TYPE => "sub_u8",
      U16_TYPE => "sub_u16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location,
   })
}

fn replace_mul(
   operand: ExpressionId,
   location: SourceInfo,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let operand_type = program.ast.expressions[operand].exp_type.as_ref().unwrap();
   let proc_name = match *operand_type {
      I8_TYPE => "mul_i8",
      I16_TYPE => "mul_i16",
      U8_TYPE => "mul_u8",
      U16_TYPE => "mul_u16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location,
   })
}

fn replace_shl(
   operand: ExpressionId,
   location: SourceInfo,
   program: &Program,
   interner: &Interner,
) -> Option<ExpressionNode> {
   let operand_type = program.ast.expressions[operand].exp_type.as_ref().unwrap();
   let proc_name = match *operand_type {
      I8_TYPE => "shl_i8",
      I16_TYPE => "shl_i16",
      U8_TYPE => "shl_u8",
      U16_TYPE => "shl_u16",
      _ => return None,
   };
   let proc_id = program.procedure_name_table[&interner.reverse_lookup(proc_name).unwrap()];
   Some(ExpressionNode {
      expression: Expression::BoundFcnLiteral(proc_id, Box::new([])),
      exp_type: Some(ExpressionType::ProcedureItem(proc_id, Box::new([]))),
      location,
   })
}

pub fn replace_nonnative_casts_and_unique_overflow(program: &mut Program, interner: &Interner, target: Target) {
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
            BinOp::Add if target == Target::Qbe => replace_add(lhs, v.location, program, interner),
            BinOp::Subtract if target == Target::Qbe => replace_sub(lhs, v.location, program, interner),
            BinOp::Multiply if target == Target::Qbe => replace_mul(lhs, v.location, program, interner),
            BinOp::BitwiseLeftShift if target == Target::Qbe => replace_shl(lhs, v.location, program, interner),
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

pub fn kill_zst_assignments(program: &mut Program, target: Target) {
   for cfg in program.procedure_bodies.values_mut().map(|x| &mut x.cfg) {
      for bb in cfg.bbs.iter_mut() {
         // This feels pretty inefficient :(
         // do this at cfg construction time?
         // at the very least, most basic blocks have no such assignments
         bb.instructions = bb
            .instructions
            .drain(..)
            .flat_map(|x| match x {
               CfgInstruction::Assignment(lhs, rhs) => {
                  let rhs_t = program.ast.expressions[rhs].exp_type.as_ref().unwrap();
                  if sizeof_type_mem(rhs_t, &program.user_defined_types, target) == 0 {
                     let lhs_se = expression_could_have_side_effects(lhs, &program.ast.expressions);
                     let rhs_se = expression_could_have_side_effects(rhs, &program.ast.expressions);
                     [
                        Some(CfgInstruction::Expression(lhs)).filter(|_| lhs_se),
                        Some(CfgInstruction::Expression(rhs)).filter(|_| rhs_se),
                     ]
                  } else {
                     [Some(x), None]
                  }
               }
               _ => [Some(x), None],
            })
            .flatten()
            .collect();
      }
   }
}
