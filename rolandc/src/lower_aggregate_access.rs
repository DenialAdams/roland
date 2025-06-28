use crate::parse::{BinOp, Expression, ExpressionId, ExpressionNode};
use crate::size_info::sizeof_type_mem;
use crate::type_data::{ExpressionType, IntType, IntWidth};
use crate::{Program, Target};

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

            if matches!(
               program.ast.expressions[index].expression,
               Expression::IntLiteral { val: 0, .. }
            ) {
               program.ast.expressions[e].expression = program.ast.expressions[array].expression.clone();
               continue;
            }

            let sizeof_inner = match program.ast.expressions[array]
               .exp_type
               .as_ref()
               .unwrap()
               .get_type_or_type_being_pointed_to()
            {
               ExpressionType::Array(x, _) => sizeof_type_mem(x, &program.user_defined_types, target),
               _ => unreachable!(),
            };
            let offset_node = if sizeof_inner == 1 {
               index
            } else {
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

               program.ast.expressions.insert(ExpressionNode {
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
               })
            };
            program.ast.expressions[e].expression = Expression::BinaryOperator {
               operator: BinOp::Add,
               lhs: array,
               rhs: offset_node,
            };
         }
         _ => (),
      }
   }
}
