use crate::interner::StrId;
use crate::parse::{BinOp, BlockNode, Expression, ExpressionNode, Program, Statement, UnOp};
use crate::type_data::{ExpressionType, ValueType};
use std::collections::HashMap;
use std::io::Write;
use std::ops::{BitAnd, BitOr, BitXor};

pub struct FoldingContext {
   pub error_count: u64,
}

pub fn fold_constants<W: Write>(program: &mut Program, err_stream: &mut W) -> u64 {
   let mut folding_context = FoldingContext { error_count: 0 };

   for procedure in program.procedures.iter_mut() {
      fold_block(&mut procedure.block, err_stream, &mut folding_context);
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
      Statement::AssignmentStatement(lhs_expr, rhs_expr) => {
         try_fold_and_replace_expr(lhs_expr, err_stream, folding_context);
         try_fold_and_replace_expr(rhs_expr, err_stream, folding_context);
      }
      Statement::BlockStatement(block) => {
         fold_block(block, err_stream, folding_context);
      }
      Statement::BreakStatement | Statement::ContinueStatement => (),
      Statement::IfElseStatement(if_expr, if_block, else_statement) => {
         try_fold_and_replace_expr(if_expr, err_stream, folding_context);
         fold_block(if_block, err_stream, folding_context);
         fold_statement(&mut else_statement.statement, err_stream, folding_context);
      }
      Statement::LoopStatement(block) => {
         fold_block(block, err_stream, folding_context);
      }
      Statement::ExpressionStatement(expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);
      }
      Statement::ReturnStatement(expr) => {
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

         if let Some(Literal::Int(v)) = extract_literal(&index.expression) {
            if v < 0 || v >= len || v >= i64::from(std::u32::MAX) {
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
      Expression::ProcedureCall(_name, exprs) => {
         for expr in exprs.iter_mut() {
            try_fold_and_replace_expr(expr, err_stream, folding_context);
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

         let lhs = extract_literal(&exprs.0.expression);
         let rhs = extract_literal(&exprs.1.expression);

         if lhs.is_none() && rhs.is_none() {
            return None;
         }

         // We only need one of LHS/RHS for some constant operations
         {
            // First we handle the non-commutative cases
            match (rhs, *op) {
               (Some(Literal::Int(0)), BinOp::Divide) => {
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
               (Some(Literal::Int(1)), BinOp::Divide) => {
                  return Some(ExpressionNode {
                     expression: exprs.0.expression.clone(),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               }
               _ => (),
            }

            let (one_literal, non_literal_expr) = if rhs.is_none() {
               (lhs.unwrap(), &exprs.1.expression)
            } else {
               (rhs.unwrap(), &exprs.0.expression)
            };

            match (one_literal, *op) {
               // TODO: this i64::MAX (in several places) is very gross. We should store literal based on actual type? Or something?
               // constant does not affect LHs
               (Literal::Int(1), BinOp::Multiply)
               | (Literal::Int(0), BinOp::Add)
               | (Literal::Bool(false), BinOp::BitwiseOr)
               | (Literal::Bool(true), BinOp::BitwiseAnd)
               | (Literal::Int(i64::MAX), BinOp::BitwiseAnd)
               | (Literal::Int(0), BinOp::BitwiseOr) => {
                  return Some(ExpressionNode {
                     expression: non_literal_expr.clone(),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               },
               (Literal::Int(i64::MAX), BinOp::BitwiseOr) => {
                  return Some(ExpressionNode {
                     expression: Expression::IntLiteral(i64::MAX),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               },
               (Literal::Int(0), BinOp::BitwiseAnd) => {
                  return Some(ExpressionNode {
                     expression: Expression::IntLiteral(0),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               },
               (Literal::Bool(true), BinOp::BitwiseOr) => {
                  return Some(ExpressionNode {
                     expression: Expression::BoolLiteral(true),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               },
               (Literal::Bool(false), BinOp::BitwiseAnd) => {
                  return Some(ExpressionNode {
                     expression: Expression::BoolLiteral(false),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               },
               (Literal::Int(0), BinOp::Multiply) => {
                  return Some(ExpressionNode {
                     expression: Expression::IntLiteral(0),
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                  });
               },
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
         }
      }
      Expression::UnaryOperator(op, expr) => {
         try_fold_and_replace_expr(expr, err_stream, folding_context);
         match op {
            // float and int
            UnOp::Negate => match extract_literal(&expr.expression) {
               Some(Literal::Int(v)) => Some(ExpressionNode {
                  expression: Expression::IntLiteral(-v),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
               }),
               Some(Literal::Bool(_)) => unreachable!(),
               Some(Literal::Float(v)) => Some(ExpressionNode {
                  expression: Expression::FloatLiteral(-v),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
               }),
               None => None,
            },
            // int and bool
            UnOp::Complement => match extract_literal(&expr.expression) {
               Some(Literal::Int(v)) => Some(ExpressionNode {
                  expression: Expression::IntLiteral(!v),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
               }),
               Some(Literal::Bool(v)) => Some(ExpressionNode {
                  expression: Expression::BoolLiteral(!v),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
               }),
               Some(Literal::Float(_)) => unreachable!(),
               None => None,
            },
            // nothing to do
            UnOp::AddressOf | UnOp::Dereference => None,
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
   }
}

fn is_const(expr: &Expression) -> bool {
   match expr {
      Expression::IntLiteral(_) => true,
      Expression::FloatLiteral(_) => true,
      Expression::BoolLiteral(_) => true,
      Expression::ArrayLiteral(exprs) => exprs.iter().all(|x| is_const(&x.expression)),
      Expression::StructLiteral(_, exprs) => exprs.iter().all(|(_, x)| is_const(&x.expression)),
      _ => false,
   }
}

#[derive(Copy, Clone, PartialEq, Debug)]
enum Literal {
   Int(i64),
   Float(f64),
   Bool(bool),
}

impl Literal {
   fn checked_add(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_add(j)?)),
         (Literal::Float(i), Literal::Float(j)) => Some(Expression::FloatLiteral(i + j)),
         _ => unreachable!(),
      }
   }

   fn checked_sub(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_sub(j)?)),
         (Literal::Float(i), Literal::Float(j)) => Some(Expression::FloatLiteral(i - j)),
         _ => unreachable!(),
      }
   }

   fn checked_mul(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_mul(j)?)),
         (Literal::Float(i), Literal::Float(j)) => Some(Expression::FloatLiteral(i * j)),
         _ => unreachable!(),
      }
   }

   fn checked_rem(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_rem(j)?)),
         (Literal::Float(i), Literal::Float(j)) => Some(Expression::FloatLiteral(i % j)),
         _ => unreachable!(),
      }
   }

   fn checked_div(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_div(j)?)),
         (Literal::Float(i), Literal::Float(j)) => Some(Expression::FloatLiteral(i / j)),
         _ => unreachable!(),
      }
   }
}

impl BitXor for Literal {
   type Output = Expression;

   fn bitxor(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Expression::IntLiteral(i ^ j),
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i ^ j),
         _ => unreachable!(),
      }
   }
}

impl BitOr for Literal {
   type Output = Expression;

   fn bitor(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Expression::IntLiteral(i | j),
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i | j),
         _ => unreachable!(),
      }
   }
}

impl BitAnd for Literal {
   type Output = Expression;

   fn bitand(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Expression::IntLiteral(i & j),
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i & j),
         _ => unreachable!(),
      }
   }
}

impl PartialOrd for Literal {
   fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => i.partial_cmp(j),
         (Literal::Float(i), Literal::Float(j)) => i.partial_cmp(j),
         _ => unreachable!(),
      }
   }
}

fn extract_literal(expr: &Expression) -> Option<Literal> {
   match expr {
      Expression::IntLiteral(x) => Some(Literal::Int(*x)),
      Expression::FloatLiteral(x) => Some(Literal::Float(*x)),
      Expression::BoolLiteral(x) => Some(Literal::Bool(*x)),
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
