use crate::interner::StrId;
use crate::parse::{BinOp, BlockNode, Expression, ExpressionNode, Program, Statement, UnOp};
use crate::type_data::{
   ExpressionType, ValueType, F32_TYPE, F64_TYPE, I16_TYPE, I32_TYPE, I64_TYPE, I8_TYPE, ISIZE_TYPE, U16_TYPE,
   U32_TYPE, U64_TYPE, U8_TYPE, USIZE_TYPE,
};
use std::collections::HashMap;
use std::io::Write;
use std::ops::{BitAnd, BitOr, BitXor, Shl, Shr};

pub struct FoldingContext {
   pub error_count: u64,
}

pub fn fold_constants<W: Write>(program: &mut Program, err_stream: &mut W) -> u64 {
   let mut folding_context = FoldingContext { error_count: 0 };

   for procedure in program.procedures.iter_mut() {
      fold_block(&mut procedure.block, err_stream, &mut folding_context);
   }

   for p_static in program.statics.iter_mut() {
      if let Some(v) = p_static.value.as_mut() {
         try_fold_and_replace_expr(v, err_stream, &mut folding_context);
      }
   }

   folding_context.error_count
}

pub fn fold_block<W: Write>(block: &mut BlockNode, err_stream: &mut W, folding_context: &mut FoldingContext) {
   for statement in block.statements.iter_mut() {
      fold_statement(&mut statement.statement, err_stream, folding_context);
   }
}

pub fn fold_statement<W: Write>(statement: &mut Statement, err_stream: &mut W, folding_context: &mut FoldingContext) {
   match statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         try_fold_and_replace_expr(lhs_expr, err_stream, folding_context);
         try_fold_and_replace_expr(rhs_expr, err_stream, folding_context);
      }
      Statement::Block(block) => {
         fold_block(block, err_stream, folding_context);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse(if_expr, if_block, else_statement) => {
         try_fold_and_replace_expr(if_expr, err_stream, folding_context);
         fold_block(if_block, err_stream, folding_context);
         fold_statement(&mut else_statement.statement, err_stream, folding_context);
      }
      Statement::For(_var, start_expr, end_expr, block, _) => {
         try_fold_and_replace_expr(start_expr, err_stream, folding_context);
         try_fold_and_replace_expr(end_expr, err_stream, folding_context);
         fold_block(block, err_stream, folding_context);
      }
      Statement::Loop(block) => {
         fold_block(block, err_stream, folding_context);
      }
      Statement::Expression(expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);
      }
      Statement::Return(expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);
      }
      Statement::VariableDeclaration(_, expr, _) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);
      }
   }
}

#[must_use]
pub fn fold_expr<W: Write>(
   expr_to_fold: &mut ExpressionNode,
   err_stream: &mut W,
   folding_context: &mut FoldingContext,
) -> Option<ExpressionNode> {
   match &mut expr_to_fold.expression {
      Expression::ArrayIndex(array, index) => {
         try_fold_and_replace_expr(array, err_stream, folding_context);
         try_fold_and_replace_expr(index, err_stream, folding_context);

         let len = match array.exp_type {
            Some(ExpressionType::Value(ValueType::Array(_, len))) => len,
            _ => unreachable!(),
         };

         // TODO @FixedPointerWidth
         if let Some(Literal::Uint32(v)) = extract_literal(index) {
            // TODO: (len should be u32/usize, not i128. and we should be validating it before now)
            // (maybe we already are?? but I don't think so)
            if i128::from(v) >= len {
               folding_context.error_count += 1;
               writeln!(
                  err_stream,
                  "At runtime, index will be {}, which is out of bounds for the array of length {}",
                  v, len,
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ array @ line {}, column {}",
                  array.expression_begin_location.line, array.expression_begin_location.col
               )
               .unwrap();
               writeln!(
                  err_stream,
                  "↳ index @ line {}, column {}",
                  index.expression_begin_location.line, index.expression_begin_location.col
               )
               .unwrap();
            } else if is_const(&array.expression) {
               let array_elems = match &mut array.expression {
                  Expression::ArrayLiteral(exprs) => exprs,
                  _ => unreachable!(),
               };

               let chosen_elem = array_elems.get_mut(v as usize).unwrap();

               return Some(ExpressionNode {
                  expression: chosen_elem.expression.clone(),
                  exp_type: chosen_elem.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
               });
            }
         }

         None
      }
      Expression::Variable(_) => None,
      Expression::ProcedureCall(_name, args) => {
         for arg in args.iter_mut() {
            try_fold_and_replace_expr(&mut arg.expr, err_stream, folding_context);
         }

         None
      }
      Expression::ArrayLiteral(_) => None,
      Expression::BoolLiteral(_) => None,
      Expression::StringLiteral(_) => None,
      Expression::IntLiteral(_) => None,
      Expression::FloatLiteral(_) => None,
      Expression::UnitLiteral => None,
      Expression::BinaryOperator(op, exprs) => {
         try_fold_and_replace_expr(&mut exprs.0, err_stream, folding_context);
         try_fold_and_replace_expr(&mut exprs.1, err_stream, folding_context);

         debug_assert!(exprs.0.exp_type == exprs.1.exp_type);

         let lhs = extract_literal(&exprs.0);
         let rhs = extract_literal(&exprs.1);

         if lhs.is_none() && rhs.is_none() {
            return None;
         }

         // We only need one of LHS/RHS for some constant operations
         {
            // First we handle the non-commutative cases
            match (rhs, *op) {
               (Some(x), BinOp::Divide) if x.is_int_zero() => {
                  folding_context.error_count += 1;
                  writeln!(err_stream, "During constant folding, got a divide by zero",).unwrap();
                  writeln!(
                     err_stream,
                     "↳ division @ line {}, column {}",
                     expr_to_fold.expression_begin_location.line, expr_to_fold.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ LHS @ line {}, column {}",
                     exprs.0.expression_begin_location.line, exprs.0.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ RHS @ line {}, column {}",
                     exprs.1.expression_begin_location.line, exprs.1.expression_begin_location.col
                  )
                  .unwrap();
                  return None;
               }
               (Some(x), BinOp::Divide) if x.is_int_one() => {
                  return Some(ExpressionNode {
                     expression: exprs.0.expression.clone(),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               _ => (),
            }

            let (one_literal, non_literal_expr) = if let Some(v) = rhs {
               (v, &exprs.0.expression)
            } else {
               (lhs.unwrap(), &exprs.1.expression)
            };

            match (one_literal, *op) {
               (x, b_op) if is_commutative_noop(x, b_op) => {
                  return Some(ExpressionNode {
                     expression: non_literal_expr.clone(),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               (x, BinOp::BitwiseOr) if x.is_int_max() => {
                  return Some(ExpressionNode {
                     expression: Expression::IntLiteral(x.int_max_value()),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               (x, BinOp::BitwiseAnd) if x.is_int_zero() => {
                  return Some(ExpressionNode {
                     expression: Expression::IntLiteral(0),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               (Literal::Bool(true), BinOp::BitwiseOr) => {
                  return Some(ExpressionNode {
                     expression: Expression::BoolLiteral(true),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               (Literal::Bool(false), BinOp::BitwiseAnd) => {
                  return Some(ExpressionNode {
                     expression: Expression::BoolLiteral(false),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               (x, BinOp::Multiply) if x.is_int_zero() => {
                  return Some(ExpressionNode {
                     expression: Expression::IntLiteral(0),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               _ => (),
            }
         }

         if lhs.is_none() || rhs.is_none() {
            return None;
         }

         let lhs = lhs.unwrap();
         let rhs = rhs.unwrap();

         match op {
            // int and float and bool
            BinOp::Equality => Some(ExpressionNode {
               expression: Expression::BoolLiteral(lhs == rhs),
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::NotEquality => Some(ExpressionNode {
               expression: Expression::BoolLiteral(lhs != rhs),
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            // int and float
            BinOp::Add => {
               if let Some(v) = lhs.checked_add(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  })
               } else {
                  folding_context.error_count += 1;
                  writeln!(err_stream, "During constant folding, got overflow while adding",).unwrap();
                  writeln!(
                     err_stream,
                     "↳ addition @ line {}, column {}",
                     expr_to_fold.expression_begin_location.line, expr_to_fold.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ LHS @ line {}, column {}",
                     exprs.0.expression_begin_location.line, exprs.0.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ RHS @ line {}, column {}",
                     exprs.1.expression_begin_location.line, exprs.1.expression_begin_location.col
                  )
                  .unwrap();
                  None
               }
            }
            BinOp::Subtract => {
               if let Some(v) = lhs.checked_sub(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  })
               } else {
                  folding_context.error_count += 1;
                  writeln!(err_stream, "During constant folding, got underflow while subtracting",).unwrap();
                  writeln!(
                     err_stream,
                     "↳ subtraction @ line {}, column {}",
                     expr_to_fold.expression_begin_location.line, expr_to_fold.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ LHS @ line {}, column {}",
                     exprs.0.expression_begin_location.line, exprs.0.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ RHS @ line {}, column {}",
                     exprs.1.expression_begin_location.line, exprs.1.expression_begin_location.col
                  )
                  .unwrap();
                  None
               }
            }
            BinOp::Multiply => {
               if let Some(v) = lhs.checked_mul(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  })
               } else {
                  folding_context.error_count += 1;
                  writeln!(err_stream, "During constant folding, got overflow while multiplying",).unwrap();
                  writeln!(
                     err_stream,
                     "↳ multiplication @ line {}, column {}",
                     expr_to_fold.expression_begin_location.line, expr_to_fold.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ LHS @ line {}, column {}",
                     exprs.0.expression_begin_location.line, exprs.0.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ RHS @ line {}, column {}",
                     exprs.1.expression_begin_location.line, exprs.1.expression_begin_location.col
                  )
                  .unwrap();
                  None
               }
            }
            BinOp::Divide => {
               if let Some(v) = lhs.checked_div(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  })
               } else {
                  // Divide by 0 handled above
                  unreachable!();
               }
            }
            BinOp::Remainder => {
               if let Some(v) = lhs.checked_rem(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  })
               } else {
                  folding_context.error_count += 1;
                  writeln!(err_stream, "During constant folding, got a divide by zero",).unwrap();
                  writeln!(
                     err_stream,
                     "↳ remainder @ line {}, column {}",
                     expr_to_fold.expression_begin_location.line, expr_to_fold.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ LHS @ line {}, column {}",
                     exprs.0.expression_begin_location.line, exprs.0.expression_begin_location.col
                  )
                  .unwrap();
                  writeln!(
                     err_stream,
                     "↳ RHS @ line {}, column {}",
                     exprs.1.expression_begin_location.line, exprs.1.expression_begin_location.col
                  )
                  .unwrap();
                  None
               }
            }
            BinOp::GreaterThan => Some(ExpressionNode {
               expression: Expression::BoolLiteral(lhs > rhs),
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::LessThan => Some(ExpressionNode {
               expression: Expression::BoolLiteral(lhs < rhs),
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::GreaterThanOrEqualTo => Some(ExpressionNode {
               expression: Expression::BoolLiteral(lhs >= rhs),
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::LessThanOrEqualTo => Some(ExpressionNode {
               expression: Expression::BoolLiteral(lhs <= rhs),
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            // int and bool
            BinOp::BitwiseAnd => Some(ExpressionNode {
               expression: lhs & rhs,
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::BitwiseOr => Some(ExpressionNode {
               expression: lhs | rhs,
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::BitwiseXor => Some(ExpressionNode {
               expression: lhs ^ rhs,
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            // int
            BinOp::BitwiseLeftShift => Some(ExpressionNode {
               expression: lhs << rhs,
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::BitwiseRightShift => Some(ExpressionNode {
               expression: lhs >> rhs,
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            // bool
            BinOp::LogicalAnd => Some(ExpressionNode {
               expression: lhs & rhs,
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
            BinOp::LogicalOr => Some(ExpressionNode {
               expression: lhs | rhs,
               exp_type: expr_to_fold.exp_type.take(),
               expression_begin_location: expr_to_fold.expression_begin_location,
            }),
         }
      }
      Expression::UnaryOperator(op, expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);
         if let Some(literal) = extract_literal(expr) {
            match op {
               // float and signed int
               UnOp::Negate => Some(ExpressionNode {
                  expression: literal.negate(),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
               }),
               // int and bool
               UnOp::Complement => Some(ExpressionNode {
                  expression: literal.complement(),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
               }),
               // nothing to do
               UnOp::AddressOf | UnOp::Dereference => None,
            }
         } else {
            None
         }
      }
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter_mut() {
            try_fold_and_replace_expr(expr, err_stream, folding_context);
         }

         None
      }
      Expression::FieldAccess(field_names, expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);

         if is_const(&expr.expression) {
            let mut struct_literal = &expr.expression;
            // drill to innermost struct
            for field_name in field_names.iter().take(field_names.len() - 1) {
               match struct_literal {
                  Expression::StructLiteral(_, fields) => {
                     // We want O(1) field access in other places- consider unifying, perhaps at parse time? TODO
                     let map: HashMap<StrId, &ExpressionNode> = fields.iter().map(|x| (x.0, &x.1)).collect();
                     struct_literal = &map.get(field_name).unwrap().expression;
                  }
                  _ => unreachable!(),
               }
            }

            match struct_literal {
               Expression::StructLiteral(_, fields) => {
                  // We want O(1) field access in other places- consider unifying, perhaps at parse time? TODO
                  let map: HashMap<StrId, &ExpressionNode> = fields.iter().map(|x| (x.0, &x.1)).collect();
                  let inner_node = map.get(field_names.last().unwrap()).unwrap();
                  Some(ExpressionNode {
                     expression: inner_node.expression.clone(),
                     exp_type: inner_node.exp_type.clone(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  })
               }
               _ => unreachable!(),
            }
         } else {
            None
         }
      }
      Expression::Extend(_, expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);

         None
      }
      Expression::Truncate(_, expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);

         None
      }
      Expression::Transmute(_, expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);

         None
      }
      Expression::EnumLiteral(_, _) => None,
   }
}

pub fn is_const(expr: &Expression) -> bool {
   match expr {
      Expression::EnumLiteral(_, _) => true,
      Expression::IntLiteral(_) => true,
      Expression::FloatLiteral(_) => true,
      Expression::BoolLiteral(_) => true,
      Expression::ArrayLiteral(exprs) => exprs.iter().all(|x| is_const(&x.expression)),
      Expression::StructLiteral(_, exprs) => exprs.iter().all(|(_, x)| is_const(&x.expression)),
      // Tentative - I'm not sure how we'll handle transmuting of unalike types in the wasm backend,
      // but conceptually this seems sound
      Expression::Transmute(_, expr) => is_const(&expr.expression),
      _ => false,
   }
}

#[derive(Copy, Clone, PartialEq, Debug)]
enum Literal {
   Int8(i8),
   Int16(i16),
   Int32(i32),
   Int64(i64),
   Uint8(u8),
   Uint16(u16),
   Uint32(u32),
   Uint64(u64),
   Float64(f64),
   Float32(f32),
   Bool(bool),
   Enum(StrId, StrId),
}

impl Literal {
   fn int_max_value(self) -> i128 {
      match self {
         Literal::Int8(_) => i128::from(i8::MAX),
         Literal::Int16(_) => i128::from(i16::MAX),
         Literal::Int32(_) => i128::from(i32::MAX),
         Literal::Int64(_) => i128::from(i64::MAX),
         Literal::Uint8(_) => i128::from(u8::MAX),
         Literal::Uint16(_) => i128::from(u16::MAX),
         Literal::Uint32(_) => i128::from(u32::MAX),
         Literal::Uint64(_) => i128::from(u64::MAX),
         _ => unreachable!(),
      }
   }

   fn is_int_max(self) -> bool {
      matches!(
         self,
         Literal::Int8(i8::MAX)
            | Literal::Int16(i16::MAX)
            | Literal::Int32(i32::MAX)
            | Literal::Int64(i64::MAX)
            | Literal::Uint8(u8::MAX)
            | Literal::Uint16(u16::MAX)
            | Literal::Uint32(u32::MAX)
            | Literal::Uint64(u64::MAX)
      )
   }
   fn is_int_zero(self) -> bool {
      matches!(
         self,
         Literal::Int8(0)
            | Literal::Int16(0)
            | Literal::Int32(0)
            | Literal::Int64(0)
            | Literal::Uint8(0)
            | Literal::Uint16(0)
            | Literal::Uint32(0)
            | Literal::Uint64(0)
      )
   }

   fn is_int_one(self) -> bool {
      matches!(
         self,
         Literal::Int8(1)
            | Literal::Int16(1)
            | Literal::Int32(1)
            | Literal::Int64(1)
            | Literal::Uint8(1)
            | Literal::Uint16(1)
            | Literal::Uint32(1)
            | Literal::Uint64(1)
      )
   }

   fn checked_add(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_add(j)?))),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i + j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i - j))),
         _ => unreachable!(),
      }
   }

   fn checked_sub(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_sub(j)?))),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i - j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i - j))),
         _ => unreachable!(),
      }
   }

   fn checked_mul(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_mul(j)?))),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_mul(j)?))),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_mul(j)?))),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_mul(j)?))),
         (Literal::Uint64(i), Literal::Uint64(j)) => {
            Some(Expression::IntLiteral(i.checked_mul(j)?.try_into().unwrap()))
         }
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_mul(j)?))),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_mul(j)?))),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_mul(j)?))),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i * j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i * j))),
         _ => unreachable!(),
      }
   }

   fn checked_rem(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_rem(j)?))),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i % j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i % j))),
         _ => unreachable!(),
      }
   }

   fn checked_div(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral(i128::from(i.checked_div(j)?))),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i / j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i / j))),
         _ => unreachable!(),
      }
   }

   fn negate(self) -> Expression {
      match self {
         Literal::Int64(i) => Expression::IntLiteral(i128::from(-i)),
         Literal::Int32(i) => Expression::IntLiteral(i128::from(-i)),
         Literal::Int16(i) => Expression::IntLiteral(i128::from(-i)),
         Literal::Int8(i) => Expression::IntLiteral(i128::from(-i)),
         Literal::Float64(i) => Expression::FloatLiteral(-i),
         Literal::Float32(i) => Expression::FloatLiteral(f64::from(-i)),
         _ => unreachable!(),
      }
   }

   fn complement(self) -> Expression {
      match self {
         Literal::Int64(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Int32(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Int16(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Int8(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Uint64(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Uint32(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Uint16(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Uint8(i) => Expression::IntLiteral(i128::from(!i)),
         Literal::Bool(b) => Expression::BoolLiteral(!b),
         _ => unreachable!(),
      }
   }
}

impl BitXor for Literal {
   type Output = Expression;

   fn bitxor(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral(i128::from(i ^ j)),
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i ^ j),
         _ => unreachable!(),
      }
   }
}

impl BitOr for Literal {
   type Output = Expression;

   fn bitor(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral(i128::from(i | j)),
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i | j),
         _ => unreachable!(),
      }
   }
}

impl BitAnd for Literal {
   type Output = Expression;

   fn bitand(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral(i128::from(i & j)),
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i & j),
         _ => unreachable!(),
      }
   }
}

impl Shl for Literal {
   type Output = Expression;

   fn shl(self, rhs: Self) -> Self::Output {
      match (self, rhs) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral(i128::from(i << j)),
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral(i128::from(i << j)),
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral(i128::from(i << j)),
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral(i128::from(i << j)),
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral(i128::from(i << j)),
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral(i128::from(i << j)),
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral(i128::from(i << j)),
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral(i128::from(i << j)),
         _ => unreachable!(),
      }
   }
}

impl Shr for Literal {
   type Output = Expression;

   fn shr(self, rhs: Self) -> Self::Output {
      match (self, rhs) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral(i128::from(i >> j)),
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral(i128::from(i >> j)),
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral(i128::from(i >> j)),
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral(i128::from(i >> j)),
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral(i128::from(i >> j)),
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral(i128::from(i >> j)),
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral(i128::from(i >> j)),
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral(i128::from(i >> j)),
         _ => unreachable!(),
      }
   }
}

impl PartialOrd for Literal {
   fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => i.partial_cmp(j),
         (Literal::Int32(i), Literal::Int32(j)) => i.partial_cmp(j),
         (Literal::Int16(i), Literal::Int16(j)) => i.partial_cmp(j),
         (Literal::Int8(i), Literal::Int8(j)) => i.partial_cmp(j),
         (Literal::Uint64(i), Literal::Uint64(j)) => i.partial_cmp(j),
         (Literal::Uint32(i), Literal::Uint32(j)) => i.partial_cmp(j),
         (Literal::Uint16(i), Literal::Uint16(j)) => i.partial_cmp(j),
         (Literal::Uint8(i), Literal::Uint8(j)) => i.partial_cmp(j),
         (Literal::Float64(i), Literal::Float64(j)) => i.partial_cmp(j),
         (Literal::Float32(i), Literal::Float32(j)) => i.partial_cmp(j),
         _ => unreachable!(),
      }
   }
}

fn extract_literal(expr_node: &ExpressionNode) -> Option<Literal> {
   match expr_node.expression {
      Expression::IntLiteral(x) => {
         match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(I64_TYPE) => Some(Literal::Int64(x.try_into().unwrap())),
            ExpressionType::Value(I32_TYPE) => Some(Literal::Int32(x.try_into().unwrap())),
            ExpressionType::Value(I16_TYPE) => Some(Literal::Int16(x.try_into().unwrap())),
            ExpressionType::Value(I8_TYPE) => Some(Literal::Int8(x.try_into().unwrap())),
            // @FixedPointerWidth
            ExpressionType::Value(ISIZE_TYPE) => Some(Literal::Int32(x.try_into().unwrap())),
            ExpressionType::Value(U64_TYPE) => Some(Literal::Uint64(x.try_into().unwrap())),
            ExpressionType::Value(U32_TYPE) => Some(Literal::Uint32(x.try_into().unwrap())),
            ExpressionType::Value(U16_TYPE) => Some(Literal::Uint16(x.try_into().unwrap())),
            ExpressionType::Value(U8_TYPE) => Some(Literal::Uint8(x.try_into().unwrap())),
            // @FixedPointerWidth
            ExpressionType::Value(USIZE_TYPE) => Some(Literal::Uint32(x.try_into().unwrap())),
            _ => unreachable!(),
         }
      }
      Expression::FloatLiteral(x) => match expr_node.exp_type.as_ref().unwrap() {
         ExpressionType::Value(F64_TYPE) => Some(Literal::Float64(x)),
         ExpressionType::Value(F32_TYPE) => Some(Literal::Float32(x as f32)),
         _ => unreachable!(),
      },
      Expression::BoolLiteral(x) => Some(Literal::Bool(x)),
      Expression::EnumLiteral(x, y) => Some(Literal::Enum(x, y)),
      _ => None,
   }
}

pub fn try_fold_and_replace_expr<W: Write>(
   node: &mut ExpressionNode,
   err_stream: &mut W,
   folding_context: &mut FoldingContext,
) {
   if let Some(new_node) = fold_expr(node, err_stream, folding_context) {
      *node = new_node;
   }
}

fn is_commutative_noop(literal: Literal, op: BinOp) -> bool {
   (literal.is_int_one() & (op == BinOp::Multiply))
      || (literal.is_int_zero() & (op == BinOp::Add))
      || (literal.is_int_zero() & (op == BinOp::BitwiseOr))
      || ((literal == Literal::Bool(false)) & (op == BinOp::BitwiseOr))
      || ((literal == Literal::Bool(true)) & (op == BinOp::BitwiseAnd))
      || (literal.is_int_max() & (op == BinOp::BitwiseAnd))
}
