use crate::parse::{BinOp, Expression, ExpressionId, ExpressionNode, all_expression_pools_mut};
use crate::size_info::sizeof_type_mem;
use crate::type_data::{ExpressionType, IntType, IntWidth};
use crate::{BaseTarget, Program};

pub fn lower_aggregate_access(program: &mut Program, target: BaseTarget) {
   for ast in all_expression_pools_mut(&mut program.global_exprs, &mut program.procedure_bodies) {
      let expression_ids: Vec<ExpressionId> = ast.keys().collect();
      for e in expression_ids {
         match &ast[e].expression {
            Expression::FieldAccess(f, base) => {
               let f = *f;
               let base = *base;
               let mem_offset = match ast[base].exp_type.as_ref().unwrap().get_type_or_type_being_pointed_to() {
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
                  ast[e].expression = ast[base].expression.clone();
               } else {
                  let offset_node = ast.insert(ExpressionNode {
                     exp_type: Some(ExpressionType::Int(IntType {
                        signed: false,
                        width: IntWidth::Pointer,
                     })),
                     expression: Expression::IntLiteral {
                        val: u64::from(mem_offset),
                        synthetic: true,
                     },
                     location: ast[e].location,
                  });
                  ast[e].expression = Expression::BinaryOperator {
                     operator: BinOp::Add,
                     lhs: base,
                     rhs: offset_node,
                  };
               }
            }
            Expression::ArrayIndex { array, index } => {
               let array = *array;
               let index = *index;

               if matches!(ast[index].expression, Expression::IntLiteral { val: 0, .. }) {
                  ast[e].expression = ast[array].expression.clone();
                  continue;
               }

               let sizeof_inner = match ast[array]
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
                  let sizeof_literal_node = ast.insert(ExpressionNode {
                     exp_type: Some(ExpressionType::Int(IntType {
                        signed: false,
                        width: IntWidth::Pointer,
                     })),
                     expression: Expression::IntLiteral {
                        val: u64::from(sizeof_inner),
                        synthetic: true,
                     },
                     location: ast[e].location,
                  });

                  ast.insert(ExpressionNode {
                     exp_type: Some(ExpressionType::Int(IntType {
                        signed: false,
                        width: target.lowered_ptr_width(),
                     })),
                     expression: Expression::BinaryOperator {
                        operator: BinOp::Multiply,
                        lhs: sizeof_literal_node,
                        rhs: index,
                     },
                     location: ast[e].location,
                  })
               };
               ast[e].expression = Expression::BinaryOperator {
                  operator: BinOp::Add,
                  lhs: array,
                  rhs: offset_node,
               };
            }
            _ => (),
         }
      }
   }
}
