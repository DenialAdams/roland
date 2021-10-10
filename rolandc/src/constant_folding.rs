use crate::parse::{BlockNode, Expression, ExpressionNode, Program, Statement, BinOp, UnOp};
use std::{io::Write, mem::discriminant, ops::{BitAnd, BitOr, BitXor}};

struct FoldingContext {
   error_count: u64,
}

pub fn fold_constants<W: Write>(program: &mut Program, err_stream: &mut W) -> u64 {
   let mut error_count = 0;

   let mut validation_context = FoldingContext {
      error_count,
   };

   for procedure in program.procedures.iter_mut() {
      fold_block(&mut procedure.block, err_stream);
   }

   error_count
}

pub fn fold_block<W: Write>(block: &mut BlockNode, err_stream: &mut W) {
   for statement in block.statements.iter_mut() {
      fold_statement(&mut statement.statement, err_stream);
   }
}

pub fn fold_statement<W: Write>(statement: &mut Statement, err_stream: &mut W,) {
   match statement {
      Statement::AssignmentStatement(lhs_expr, rhs_expr) => {
         try_fold_and_replace_expr(lhs_expr, err_stream);
         try_fold_and_replace_expr(rhs_expr, err_stream);
      }
      Statement::BlockStatement(block) => {
         fold_block(block, err_stream);
      }
      Statement::BreakStatement | Statement::ContinueStatement => (),
      Statement::IfElseStatement(if_expr, if_block, else_statement) => {
         try_fold_and_replace_expr(if_expr, err_stream);
         fold_block(if_block, err_stream);
         fold_statement(&mut else_statement.statement, err_stream);
      },
      Statement::LoopStatement(block) => {
         fold_block(block, err_stream);
      },
      Statement::ExpressionStatement(expr) => {
         try_fold_and_replace_expr(expr, err_stream);
      },
      Statement::ReturnStatement(expr) => {
         try_fold_and_replace_expr(expr, err_stream);
      },
      Statement::VariableDeclaration(_, expr, _) => {
         try_fold_and_replace_expr(expr, err_stream);
      }
   }
}

#[must_use]
pub fn fold_expr<W: Write>(expr_to_fold: &mut ExpressionNode, err_stream: &mut W) -> Option<ExpressionNode> {
   match &mut expr_to_fold.expression {
      Expression::ArrayIndex(array, index) => {
         try_fold_and_replace_expr(array, err_stream);
         try_fold_and_replace_expr(index, err_stream);

         None
      }
      Expression::Variable(_) => {
         None
      }
      Expression::ProcedureCall(_name, exprs) => {
         for expr in exprs.iter_mut() {
            try_fold_and_replace_expr(expr, err_stream);
         }

         None
      },
      Expression::ArrayLiteral(_) => {
         None
      },
      Expression::BoolLiteral(_) => {
         None
      }
      Expression::StringLiteral(_) => {
         None
      },
      Expression::IntLiteral(_) => {
         None
      },
      Expression::UnitLiteral => None,
      Expression::BinaryOperator(op, exprs) => {
         try_fold_and_replace_expr(&mut exprs.0, err_stream);
         try_fold_and_replace_expr(&mut exprs.1, err_stream);

         let lhs = extract_literal(&exprs.0.expression);
         let rhs = extract_literal(&exprs.1.expression);

         if lhs.is_none() || rhs.is_none() {
            return None;
         }

         let lhs = lhs.unwrap();
         let rhs = rhs.unwrap();

         debug_assert!(discriminant(&lhs) == discriminant(&rhs));

         match op {
            // int and float and bool
            BinOp::Equality => {
               Some(ExpressionNode {
                  expression: Expression::BoolLiteral(lhs == rhs),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            }
            BinOp::NotEquality => {
               Some(ExpressionNode {
                  expression: Expression::BoolLiteral(lhs != rhs),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
            // int and float
            BinOp::Add => {
               if let Some(v) = lhs.checked_add(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                   })
               } else {
                  unimplemented!();
                  None
               }
            },
            BinOp::Subtract => {
               if let Some(v) = lhs.checked_sub(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                   })
               } else {
                  unimplemented!();
                  None
               }
            },
            BinOp::Multiply => {
               if let Some(v) = lhs.checked_mul(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                   })
               } else {
                  unimplemented!();
                  None
               }
            },
            BinOp::Divide => {
               if let Some(v) = lhs.checked_div(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                   })
               } else {
                  unimplemented!();
                  None
               }
            },
            BinOp::Remainder => {
               if let Some(v) = lhs.checked_rem(rhs) {
                  Some(ExpressionNode {
                     expression: v,
                     exp_type: expr_to_fold.exp_type.take(),
                     expression_begin_location: expr_to_fold.expression_begin_location,
                   })
               } else {
                  unimplemented!();
                  None
               }
            },
            BinOp::GreaterThan => {
               Some(ExpressionNode {
                  expression: Expression::BoolLiteral(lhs > rhs),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
            BinOp::LessThan => {
               Some(ExpressionNode {
                  expression: Expression::BoolLiteral(lhs < rhs),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
            BinOp::GreaterThanOrEqualTo => {
               Some(ExpressionNode {
                  expression: Expression::BoolLiteral(lhs >= rhs),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
            BinOp::LessThanOrEqualTo => {
               Some(ExpressionNode {
                  expression: Expression::BoolLiteral(lhs <= rhs),
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
            // int and bool
            BinOp::BitwiseAnd => {
               Some(ExpressionNode {
                  expression: lhs & rhs,
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
            BinOp::BitwiseOr => {
               Some(ExpressionNode {
                  expression: lhs | rhs,
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
            BinOp::BitwiseXor => {
               Some(ExpressionNode {
                  expression: lhs ^ rhs,
                  exp_type: expr_to_fold.exp_type.take(),
                  expression_begin_location: expr_to_fold.expression_begin_location,
                })
            },
        }
      },
      Expression::UnaryOperator(op, expr) => {
         try_fold_and_replace_expr(expr, err_stream);
         match op {
            // float and int
            UnOp::Negate => match extract_literal(&expr.expression) {
                  Some(Literal::Int(v)) => Some(ExpressionNode {
                    expression: Expression::IntLiteral(-v),
                    exp_type: expr_to_fold.exp_type.take(),
                    expression_begin_location: expr_to_fold.expression_begin_location,
                  }),
                  Some(Literal::Bool(_)) => unreachable!(),
                  Some(Literal::Float(_)) => unimplemented!(),
                  None => None,
            }
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
               Some(Literal::Float(_)) => unimplemented!(),
               None => None,
            }
            // nothing to do
            UnOp::AddressOf | UnOp::Dereference => None,
        }
      },
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter_mut() {
            try_fold_and_replace_expr(expr, err_stream);
         }

         None
      },
      Expression::FieldAccess(_, expr) => {
         try_fold_and_replace_expr(expr, err_stream);

         None
      },
      Expression::Extend(_, expr) => {
         try_fold_and_replace_expr(expr, err_stream);

         None
      },
      Expression::Truncate(_, expr) => {
         try_fold_and_replace_expr(expr, err_stream);

         None
      },
      Expression::Transmute(_, expr) => {
         try_fold_and_replace_expr(expr, err_stream);

         None
      },
   }  
}

#[derive(PartialEq, Debug)]
enum Literal {
   Int(i64),
   Float(f64),
   Bool(bool),
}

impl Literal {
   fn checked_add(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_add(j)?)),
         (Literal::Float(i), Literal::Float(j)) => todo!(),
         _ => unreachable!(),
      }
   }

   fn checked_sub(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_sub(j)?)),
         (Literal::Float(i), Literal::Float(j)) => todo!(),
         _ => unreachable!(),
      }
   }

   fn checked_mul(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_mul(j)?)),
         (Literal::Float(i), Literal::Float(j)) => todo!(),
         _ => unreachable!(),
      }
   }

   fn checked_rem(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_rem(j)?)),
         (Literal::Float(i), Literal::Float(j)) => todo!(),
         _ => unreachable!(),
      }
   }

   fn checked_div(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int(i), Literal::Int(j)) => Some(Expression::IntLiteral(i.checked_div(j)?)),
         (Literal::Float(i), Literal::Float(j)) => todo!(),
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
      Expression::BoolLiteral(x) => Some(Literal::Bool(*x)),
      _ => None,
   }
}

pub fn try_fold_and_replace_expr<W: Write>(node: &mut ExpressionNode, err_stream: &mut W) {
   if let Some(new_node) = fold_expr(node, err_stream) {
      *node = new_node;
   }
}
