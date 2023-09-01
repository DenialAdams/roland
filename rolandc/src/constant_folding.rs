use std::collections::HashMap;
use std::convert::TryInto;
use std::ops::{BitAnd, BitOr, BitXor};

use slotmap::SecondaryMap;

use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_warn};
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, BinOp, BlockNode, CastType, EnumId, Expression, ExpressionId, ExpressionNode, ExpressionPool,
   ProcImplSource, ProcedureId, Program, Statement, StatementId, UnOp, UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::ProcedureInfo;
use crate::source_info::SourceInfo;
use crate::type_data::{
   ExpressionType, F32_TYPE, F64_TYPE, I16_TYPE, I32_TYPE, I64_TYPE, I8_TYPE, ISIZE_TYPE, U16_TYPE, U32_TYPE, U64_TYPE,
   U8_TYPE, USIZE_TYPE,
};

pub struct FoldingContext<'a> {
   pub ast: &'a mut AstPool,
   pub procedure_info: &'a SecondaryMap<ProcedureId, ProcedureInfo>,
   pub user_defined_types: &'a UserDefinedTypeInfo,
   pub const_replacements: &'a HashMap<VariableId, ExpressionId>,
   pub current_proc_name: Option<StrId>,
}

pub fn fold_constants(program: &mut Program, err_manager: &mut ErrorManager, interner: &Interner) {
   let mut const_replacements: HashMap<VariableId, ExpressionId> = HashMap::new();

   for p_const in program.consts.drain(..) {
      const_replacements.insert(p_const.var_id, p_const.value);
   }

   let mut folding_context = FoldingContext {
      ast: &mut program.ast,
      procedure_info: &program.procedure_info,
      user_defined_types: &program.user_defined_types,
      const_replacements: &const_replacements,
      current_proc_name: None,
   };

   for p_static in program.global_info.values().filter(|x| x.initializer.is_some()) {
      if let Some(v) = p_static.initializer.as_ref().copied() {
         try_fold_and_replace_expr(v, err_manager, &mut folding_context, interner);
         let v = &folding_context.ast.expressions[v];
         if !is_const(&v.expression, &folding_context.ast.expressions) {
            rolandc_error!(
               err_manager,
               v.location,
               "Value of static `{}` can't be constant folded. Hint: Either simplify the expression, or initialize it yourself on program start.",
               interner.lookup(p_static.name),
            );
         }
      }
   }

   for si in program.user_defined_types.struct_info.iter() {
      for field_with_default in si.1.default_values.iter() {
         try_fold_and_replace_expr(*field_with_default.1, err_manager, &mut folding_context, interner);
         let v = &folding_context.ast.expressions[*field_with_default.1];
         if !crate::constant_folding::is_const(&v.expression, &folding_context.ast.expressions) {
            rolandc_error!(
               err_manager,
               v.location,
               "Default value of struct field `{}` can't be constant folded.",
               interner.lookup(*field_with_default.0),
            );
         }
      }
   }

   for procedure in program.procedures.values_mut() {
      if let ProcImplSource::Body(block) = &procedure.proc_impl {
         folding_context.current_proc_name = Some(procedure.definition.name.str);
         fold_block(block, err_manager, &mut folding_context, interner);
      }
   }
}

pub fn fold_block(
   block: &BlockNode,
   err_manager: &mut ErrorManager,
   folding_context: &mut FoldingContext,
   interner: &Interner,
) {
   for statement in block.statements.iter().copied() {
      fold_statement(statement, err_manager, folding_context, interner);
   }
}

pub fn fold_statement(
   statement: StatementId,
   err_manager: &mut ErrorManager,
   folding_context: &mut FoldingContext,
   interner: &Interner,
) {
   let the_statement = std::mem::replace(
      &mut folding_context.ast.statements[statement].statement,
      Statement::Break,
   );
   match &the_statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         try_fold_and_replace_expr(*lhs_expr, err_manager, folding_context, interner);
         try_fold_and_replace_expr(*rhs_expr, err_manager, folding_context, interner);
      }
      Statement::Block(block) => {
         fold_block(block, err_manager, folding_context, interner);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse(if_expr, if_block, else_statement) => {
         try_fold_and_replace_expr(*if_expr, err_manager, folding_context, interner);
         fold_block(if_block, err_manager, folding_context, interner);
         fold_statement(*else_statement, err_manager, folding_context, interner);

         // We could also prune dead branches here
         let if_expr_d = &folding_context.ast.expressions[*if_expr];
         if let Some(Literal::Bool(false)) = extract_literal(if_expr_d) {
            rolandc_warn!(err_manager, if_expr_d.location, "This condition will always be false");
         } else if let Some(Literal::Bool(true)) = extract_literal(if_expr_d) {
            rolandc_warn!(err_manager, if_expr_d.location, "This condition will always be true");
         }
      }
      Statement::Loop(block) => {
         fold_block(block, err_manager, folding_context, interner);
      }
      Statement::Expression(expr_id) => {
         try_fold_and_replace_expr(*expr_id, err_manager, folding_context, interner);

         let expression = &folding_context.ast.expressions[*expr_id];
         if !matches!(expression.expression, Expression::ProcedureCall { .. }) {
            rolandc_warn!(
               err_manager,
               expression.location,
               "The result of this expression is not consumed"
            );
         }
      }
      Statement::Return(expr) => {
         try_fold_and_replace_expr(*expr, err_manager, folding_context, interner);
      }
      Statement::VariableDeclaration(_, _, _, _) => unreachable!(),
      Statement::For { .. } | Statement::While(_, _) => unreachable!(),
      Statement::Defer(_) => unreachable!(),
   }
   folding_context.ast.statements[statement].statement = the_statement;
}

pub fn try_fold_and_replace_expr(
   node: ExpressionId,
   err_manager: &mut ErrorManager,
   folding_context: &mut FoldingContext,
   interner: &Interner,
) {
   if let Some(new_node) = fold_expr(node, err_manager, folding_context, interner) {
      folding_context.ast.expressions[node].expression = new_node;
   }
}

#[must_use]
fn fold_expr(
   expr_index: ExpressionId,
   err_manager: &mut ErrorManager,
   folding_context: &mut FoldingContext,
   interner: &Interner,
) -> Option<Expression> {
   let the_expr = std::mem::replace(
      &mut folding_context.ast.expressions[expr_index],
      ExpressionNode {
         expression: Expression::UnitLiteral,
         exp_type: None,
         location: SourceInfo::dummy(),
      },
   );
   let new_expr = fold_expr_inner(&the_expr, err_manager, folding_context, interner);
   folding_context.ast.expressions[expr_index] = the_expr;

   new_expr
}

fn fold_expr_inner(
   expr: &ExpressionNode,
   err_manager: &mut ErrorManager,
   folding_context: &mut FoldingContext,
   interner: &Interner,
) -> Option<Expression> {
   let expr_to_fold_location = expr.location;
   let expr_type = expr.exp_type.as_ref().unwrap();
   match &expr.expression {
      Expression::ArrayIndex { array, index } => {
         try_fold_and_replace_expr(*array, err_manager, folding_context, interner);
         try_fold_and_replace_expr(*index, err_manager, folding_context, interner);

         let array = &folding_context.ast.expressions[*array];
         let index = &folding_context.ast.expressions[*index];

         let Some(ExpressionType::Array(_, len)) = array.exp_type else {
            unreachable!()
         };

         // TODO @FixedPointerWidth
         if let Some(Literal::Uint32(v)) = extract_literal(index) {
            if v >= len {
               rolandc_error!(
                  err_manager,
                  expr_to_fold_location,
                  "At runtime, index will be {}, which is out of bounds for the array of length {}",
                  v,
                  len,
               );
            } else if is_const(&array.expression, &folding_context.ast.expressions) {
               let Expression::ArrayLiteral(array_elems) = &array.expression else {
                  unreachable!();
               };

               let chosen_elem_expr = folding_context
                  .ast
                  .expressions
                  .get(array_elems[v as usize])
                  .unwrap()
                  .expression
                  .clone();

               return Some(chosen_elem_expr);
            }
         }

         None
      }
      Expression::Variable(x) => {
         if let Some(replacement_index) = folding_context.const_replacements.get(x).copied() {
            return Some(folding_context.ast.expressions[replacement_index].expression.clone());
         }

         None
      }
      Expression::ProcedureCall { args, proc_expr } => {
         try_fold_and_replace_expr(*proc_expr, err_manager, folding_context, interner);
         for arg in args.iter().map(|x| x.expr) {
            try_fold_and_replace_expr(arg, err_manager, folding_context, interner);
         }

         fold_builtin_call(*proc_expr, interner, folding_context)
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            try_fold_and_replace_expr(*expr, err_manager, folding_context, interner);
         }

         None
      }
      Expression::BoolLiteral(_) => None,
      Expression::StringLiteral(_) => None,
      Expression::IntLiteral { val, .. } => {
         let val = *val;
         let overflowing_literal = match expr_type {
            &I8_TYPE => (val as i64) > i64::from(i8::MAX) || (val as i64) < i64::from(i8::MIN),
            &I16_TYPE => (val as i64) > i64::from(i16::MAX) || (val as i64) < i64::from(i16::MIN),
            &I32_TYPE => (val as i64) > i64::from(i32::MAX) || (val as i64) < i64::from(i32::MIN),
            // @FixedPointerWidth
            &ISIZE_TYPE => (val as i64) > i64::from(i32::MAX) || (val as i64) < i64::from(i32::MIN),
            &I64_TYPE => false,
            &U8_TYPE => val > u64::from(u8::MAX) || val < u64::from(u8::MIN),
            &U16_TYPE => val > u64::from(u16::MAX) || val < u64::from(u16::MIN),
            &U32_TYPE => val > u64::from(u32::MAX) || val < u64::from(u32::MIN),
            // @FixedPointerWidth
            &USIZE_TYPE | ExpressionType::Pointer(_) => val > u64::from(u32::MAX) || val < u64::from(u32::MIN),
            &U64_TYPE => false,
            _ => unreachable!(),
         };

         if overflowing_literal {
            let signed = match expr_type {
               ExpressionType::Int(x) => x.signed,
               _ => unreachable!(),
            };

            if signed {
               rolandc_error!(
                  err_manager,
                  expr_to_fold_location,
                  "Literal of type {} has value `{}` which would immediately over/underflow",
                  expr_type.as_roland_type_info_notv(
                     interner,
                     folding_context.user_defined_types,
                     folding_context.procedure_info
                  ),
                  val as i64
               );
            } else {
               rolandc_error!(
                  err_manager,
                  expr_to_fold_location,
                  "Literal of type {} has value `{}` which would immediately over/underflow",
                  expr_type.as_roland_type_info_notv(
                     interner,
                     folding_context.user_defined_types,
                     folding_context.procedure_info
                  ),
                  val
               );
            }
         }

         None
      }
      Expression::FloatLiteral(_) => None,
      Expression::UnitLiteral | Expression::BoundFcnLiteral(_, _) => None,
      Expression::BinaryOperator {
         operator,
         lhs: lhs_id,
         rhs: rhs_id,
      } => {
         try_fold_and_replace_expr(*lhs_id, err_manager, folding_context, interner);
         try_fold_and_replace_expr(*rhs_id, err_manager, folding_context, interner);

         let lhs_expr = &folding_context.ast.expressions[*lhs_id];
         let rhs_expr = &folding_context.ast.expressions[*rhs_id];

         let lhs_could_have_side_effects =
            expression_could_have_side_effects(*lhs_id, &folding_context.ast.expressions);
         let rhs_could_have_side_effects =
            expression_could_have_side_effects(*rhs_id, &folding_context.ast.expressions);

         // For some cases, we don't care if either operand is literal
         if !lhs_could_have_side_effects && !rhs_could_have_side_effects && lhs_expr.expression == rhs_expr.expression {
            match operator {
               BinOp::Divide if !matches!(expr_type, ExpressionType::Float(_)) => {
                  return Some(Expression::IntLiteral {
                     val: 1,
                     synthetic: true,
                  });
               }
               BinOp::BitwiseXor => {
                  let expr = match expr_type {
                     ExpressionType::Bool => Expression::BoolLiteral(false),
                     ExpressionType::Int { .. } => Expression::IntLiteral {
                        val: 0,
                        synthetic: true,
                     },
                     _ => unreachable!(),
                  };
                  return Some(expr);
               }
               BinOp::GreaterThan | BinOp::LessThan if !matches!(expr_type, ExpressionType::Float(_)) => {
                  return Some(Expression::BoolLiteral(false));
               }
               BinOp::Equality | BinOp::GreaterThanOrEqualTo | BinOp::LessThanOrEqualTo
                  if !matches!(expr_type, ExpressionType::Float(_)) =>
               {
                  return Some(Expression::BoolLiteral(true));
               }
               BinOp::LogicalAnd | BinOp::LogicalOr | BinOp::BitwiseAnd | BinOp::BitwiseOr => {
                  let new_expr = lhs_expr.expression.clone();
                  return Some(new_expr);
               }
               _ => (),
            }
         }

         debug_assert!(lhs_expr.exp_type == rhs_expr.exp_type);

         let lhs = extract_literal(lhs_expr);
         let rhs = extract_literal(rhs_expr);

         if lhs.is_none() && rhs.is_none() {
            return None;
         }

         // We only need one of LHS/RHS for some constant operations
         {
            // First we handle the non-commutative cases
            match (rhs, operator) {
               (Some(x), BinOp::Divide) if x.is_int_zero() => {
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "During constant folding, got a divide by zero",
                  );
                  return None;
               }
               (Some(x), BinOp::Divide) if x.is_int_one() => {
                  let new_expr = lhs_expr.expression.clone();
                  return Some(new_expr);
               }
               (Some(x), BinOp::GreaterThanOrEqualTo) if x.is_int_min() => {
                  return Some(Expression::BoolLiteral(true));
               }
               (Some(x), BinOp::LessThanOrEqualTo) if x.is_int_max() => {
                  return Some(Expression::BoolLiteral(true));
               }
               (Some(x), BinOp::GreaterThan) if x.is_int_max() => {
                  return Some(Expression::BoolLiteral(false));
               }
               (Some(x), BinOp::LessThan) if x.is_int_min() => {
                  return Some(Expression::BoolLiteral(false));
               }
               _ => (),
            }

            match (lhs, operator) {
               (Some(x), BinOp::GreaterThanOrEqualTo) if x.is_int_max() => {
                  return Some(Expression::BoolLiteral(true));
               }
               (Some(x), BinOp::LessThanOrEqualTo) if x.is_int_min() => {
                  return Some(Expression::BoolLiteral(true));
               }
               (Some(x), BinOp::GreaterThan) if x.is_int_min() => {
                  return Some(Expression::BoolLiteral(false));
               }
               (Some(x), BinOp::LessThan) if x.is_int_max() => {
                  return Some(Expression::BoolLiteral(false));
               }
               _ => (),
            }

            let (one_literal, non_literal_expr, non_literal_side_effects) = if let Some(v) = rhs {
               (v, &lhs_expr.expression, lhs_could_have_side_effects)
            } else {
               (lhs.unwrap(), &rhs_expr.expression, rhs_could_have_side_effects)
            };

            if is_commutative_noop(one_literal, *operator) {
               let new_expr = non_literal_expr.clone();
               return Some(new_expr);
            } else if !non_literal_side_effects {
               match (one_literal, operator) {
                  (x, BinOp::BitwiseOr) if x.is_int_max() => {
                     return Some(Expression::IntLiteral {
                        val: x.int_max_value(),
                        synthetic: true,
                     });
                  }
                  (x, BinOp::BitwiseAnd) if x.is_int_zero() => {
                     return Some(Expression::IntLiteral {
                        val: 0,
                        synthetic: true,
                     });
                  }
                  (Literal::Bool(true), BinOp::BitwiseOr) => {
                     return Some(Expression::BoolLiteral(true));
                  }
                  (Literal::Bool(false), BinOp::BitwiseAnd) => {
                     return Some(Expression::BoolLiteral(false));
                  }
                  (Literal::Bool(true), BinOp::LogicalOr) => {
                     return Some(Expression::BoolLiteral(true));
                  }
                  (Literal::Bool(false), BinOp::LogicalAnd) => {
                     return Some(Expression::BoolLiteral(false));
                  }
                  (x, BinOp::Multiply) if x.is_int_zero() => {
                     return Some(Expression::IntLiteral {
                        val: 0,
                        synthetic: true,
                     });
                  }
                  _ => (),
               }
            }
         }

         if lhs.is_none() || rhs.is_none() {
            return None;
         }

         let lhs = lhs.unwrap();
         let rhs = rhs.unwrap();

         match operator {
            // int and float and bool
            BinOp::Equality => Some(Expression::BoolLiteral(lhs == rhs)),
            BinOp::NotEquality => Some(Expression::BoolLiteral(lhs != rhs)),
            // int and float
            BinOp::Add => {
               if let Some(v) = lhs.checked_add(rhs) {
                  Some(v)
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "During constant folding, got overflow while adding",
                  );
                  None
               }
            }
            BinOp::Subtract => {
               if let Some(v) = lhs.checked_sub(rhs) {
                  Some(v)
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "During constant folding, got overflow while subtracting",
                  );
                  None
               }
            }
            BinOp::Multiply => {
               if let Some(v) = lhs.checked_mul(rhs) {
                  Some(v)
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "During constant folding, got overflow while multiplying",
                  );
                  None
               }
            }
            BinOp::Divide => {
               if let Some(v) = lhs.checked_div(rhs) {
                  Some(v)
               } else {
                  // Divide by 0 handled above
                  unreachable!();
               }
            }
            BinOp::Remainder => {
               if let Some(v) = lhs.checked_rem(rhs) {
                  Some(v)
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "During constant folding, got a divide by zero",
                  );
                  None
               }
            }
            BinOp::GreaterThan => Some(Expression::BoolLiteral(lhs > rhs)),
            BinOp::LessThan => Some(Expression::BoolLiteral(lhs < rhs)),
            BinOp::GreaterThanOrEqualTo => Some(Expression::BoolLiteral(lhs >= rhs)),
            BinOp::LessThanOrEqualTo => Some(Expression::BoolLiteral(lhs <= rhs)),
            // int and bool
            BinOp::BitwiseAnd => Some(lhs & rhs),
            BinOp::BitwiseOr => Some(lhs | rhs),
            BinOp::BitwiseXor => Some(lhs ^ rhs),
            // int
            BinOp::BitwiseLeftShift => {
               if let Some(v) = lhs.checked_shl(rhs) {
                  Some(v)
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "During constant folding, got a bad left shift",
                  );
                  None
               }
            }
            BinOp::BitwiseRightShift => {
               if let Some(v) = lhs.checked_shr(rhs) {
                  Some(v)
               } else {
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "During constant folding, got a bad right shift",
                  );
                  None
               }
            }
            // bool
            BinOp::LogicalAnd => Some(lhs & rhs),
            BinOp::LogicalOr => Some(lhs | rhs),
         }
      }
      Expression::UnaryOperator(op, expr) => {
         if *op == UnOp::Negate {
            // THE POINT:
            // We want "-128" to be one value, not the negation of 128
            // Why? Because:
            // let x: i8 = -128;
            // 128 is > than the max we can store in an i8, but -128 just fits.
            // So, we match expectations by applying the negation BEFORE
            // we check the literal for overflow/underflow
            let f_expr = &mut folding_context.ast.expressions[*expr];
            if let Expression::IntLiteral {
               val: x,
               synthetic: false,
            } = &mut f_expr.expression
            {
               if *x > (i64::MAX as u64 + 1) {
                  // This negation is impossible, so have to die
                  rolandc_error!(
                     err_manager,
                     expr_to_fold_location,
                     "Literal of type {} has value `-{}` which would immediately underflow",
                     f_expr.exp_type.as_ref().unwrap().as_roland_type_info_notv(
                        interner,
                        folding_context.user_defined_types,
                        folding_context.procedure_info
                     ),
                     *x,
                  );
                  return None;
               }
               let val = (*x as i64).wrapping_neg() as u64;
               *x = val;

               // Run the fold anyway, for the base error check
               let _fold_result = fold_expr(*expr, err_manager, folding_context, interner);

               return Some(Expression::IntLiteral { val, synthetic: true });
            }
         }

         try_fold_and_replace_expr(*expr, err_manager, folding_context, interner);

         let expr = &folding_context.ast.expressions[*expr];

         if let Some(literal) = extract_literal(expr) {
            match op {
               // float and signed int
               UnOp::Negate => {
                  if let Some(v) = literal.checked_negate() {
                     Some(v)
                  } else {
                     rolandc_error!(
                        err_manager,
                        expr_to_fold_location,
                        "During constant folding, tried to negate the minimum value of a signed integer"
                     );
                     None
                  }
               }
               // int and bool
               UnOp::Complement => Some(literal.complement()),
               // nothing to do
               UnOp::AddressOf | UnOp::Dereference => None,
            }
         } else if matches!(expr.expression, Expression::BoundFcnLiteral(_, _)) {
            Some(expr.expression.clone())
         } else {
            None
         }
      }
      Expression::StructLiteral(_, field_exprs) => {
         for expr in field_exprs.iter().flat_map(|x| x.1) {
            try_fold_and_replace_expr(*expr, err_manager, folding_context, interner);
         }

         None
      }
      Expression::FieldAccess(field_name, expr) => {
         try_fold_and_replace_expr(*expr, err_manager, folding_context, interner);

         if expression_could_have_side_effects(*expr, &folding_context.ast.expressions) {
            None
         } else {
            let expr = &folding_context.ast.expressions[*expr];

            // Handle the case where we're getting the length of an array
            // (only requires type information, no constant expressions)
            match expr.exp_type.as_ref().unwrap() {
               ExpressionType::Array(_, len) => {
                  // Arrays only have one possible field, length
                  return Some(Expression::IntLiteral {
                     val: u64::from(*len),
                     synthetic: true,
                  });
               }
               ExpressionType::Struct(_) | ExpressionType::Union(_) => (),
               _ => unreachable!(),
            }

            match &expr.expression {
               Expression::StringLiteral(literal_val) if interner.lookup(*field_name) == "length" => {
                  Some(Expression::IntLiteral {
                     val: interner.lookup(*literal_val).len() as u64,
                     synthetic: true,
                  })
               }
               Expression::StructLiteral(_, fields) => {
                  let inner_node_expression = folding_context.ast.expressions[fields.get(field_name).unwrap().unwrap()]
                     .expression
                     .clone();
                  Some(inner_node_expression)
               }
               Expression::ArrayLiteral(_) => unreachable!(), // covered by type check above
               _ => None,                                     // Some non-constant
            }
         }
      }
      Expression::Cast { cast_type, expr, .. } => {
         try_fold_and_replace_expr(*expr, err_manager, folding_context, interner);

         let operand = &folding_context.ast.expressions[*expr];

         if expr_type == operand.exp_type.as_ref().unwrap() {
            return Some(operand.expression.clone());
         }

         if let Some(literal) = extract_literal(operand) {
            match cast_type {
               CastType::Transmute => literal.transmute(expr_type),
               CastType::As => literal.do_as(expr_type),
            }
         } else {
            None
         }
      }
      Expression::EnumLiteral(_, _) => None,
      Expression::IfX(a, b, c) => {
         try_fold_and_replace_expr(*a, err_manager, folding_context, interner);
         try_fold_and_replace_expr(*b, err_manager, folding_context, interner);
         try_fold_and_replace_expr(*c, err_manager, folding_context, interner);

         if expression_could_have_side_effects(*a, &folding_context.ast.expressions)
            || expression_could_have_side_effects(*b, &folding_context.ast.expressions)
            || expression_could_have_side_effects(*c, &folding_context.ast.expressions)
         {
            None
         } else if let Some(Literal::Bool(val)) = extract_literal(&folding_context.ast.expressions[*a]) {
            if val {
               Some(folding_context.ast.expressions[*b].expression.clone())
            } else {
               Some(folding_context.ast.expressions[*c].expression.clone())
            }
         } else {
            None
         }
      }
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}

pub fn fold_builtin_call(proc_expr: ExpressionId, interner: &Interner, fc: &FoldingContext) -> Option<Expression> {
   let (proc_name, generic_args) = match &fc.ast.expressions[proc_expr].exp_type.as_ref().unwrap() {
      ExpressionType::ProcedureItem(x, type_arguments) => (fc.procedure_info[*x].name.str, type_arguments),
      _ => return None,
   };

   match interner.lookup(proc_name) {
      "proc_name" => fc.current_proc_name.map(Expression::StringLiteral),
      "sizeof" => {
         let type_size = crate::size_info::sizeof_type_mem(&generic_args[0], fc.user_defined_types);

         Some(Expression::IntLiteral {
            val: u64::from(type_size),
            synthetic: true,
         })
      }
      "alignof" => {
         let type_alignment = crate::size_info::mem_alignment(&generic_args[0], fc.user_defined_types);

         Some(Expression::IntLiteral {
            val: u64::from(type_alignment),
            synthetic: true,
         })
      }
      "num_variants" => {
         let num_variants = match generic_args[0] {
            ExpressionType::Enum(enum_id) => fc.user_defined_types.enum_info.get(enum_id).unwrap().variants.len(),
            _ => unreachable!(),
         };

         Some(Expression::IntLiteral {
            val: num_variants as u64,
            synthetic: true,
         })
      }
      _ => None,
   }
}

pub fn is_const(expr: &Expression, expressions: &ExpressionPool) -> bool {
   match expr {
      Expression::BoundFcnLiteral(_, _) => true,
      Expression::UnitLiteral => true,
      Expression::EnumLiteral(_, _) => true,
      Expression::IntLiteral { .. } => true,
      Expression::FloatLiteral(_) => true,
      Expression::BoolLiteral(_) => true,
      Expression::ArrayLiteral(exprs) => exprs
         .iter()
         .copied()
         .all(|x| is_const(&expressions[x].expression, expressions)),
      Expression::StructLiteral(_, exprs) => exprs
         .iter()
         .flat_map(|(_, x)| x)
         .all(|x| is_const(&expressions[*x].expression, expressions)),
      Expression::StringLiteral(_) => true,
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
   Enum(EnumId, StrId),
   Unit,
}

impl Literal {
   fn int_max_value(self) -> u64 {
      match self {
         Literal::Int8(_) => u64::from(i8::MAX as u8),
         Literal::Int16(_) => u64::from(i16::MAX as u16),
         Literal::Int32(_) => u64::from(i32::MAX as u32),
         Literal::Int64(_) => i64::MAX as u64,
         Literal::Uint8(_) => u64::from(u8::MAX),
         Literal::Uint16(_) => u64::from(u16::MAX),
         Literal::Uint32(_) => u64::from(u32::MAX),
         Literal::Uint64(_) => u64::MAX,
         _ => unreachable!(),
      }
   }

   fn is_int_min(self) -> bool {
      matches!(
         self,
         Literal::Int8(i8::MIN)
            | Literal::Int16(i16::MIN)
            | Literal::Int32(i32::MIN)
            | Literal::Int64(i64::MIN)
            | Literal::Uint8(u8::MIN)
            | Literal::Uint16(u16::MIN)
            | Literal::Uint32(u32::MIN)
            | Literal::Uint64(u64::MIN)
      )
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

   fn transmute(self, target_type: &ExpressionType) -> Option<Expression> {
      Some(match (self, target_type) {
         // Transmute int to float
         (Literal::Int32(i), &F32_TYPE) => Expression::FloatLiteral(f64::from(f32::from_bits(i as u32))),
         (Literal::Uint32(i), &F32_TYPE) => Expression::FloatLiteral(f64::from(f32::from_bits(i))),
         (Literal::Int64(i), &F64_TYPE) => Expression::FloatLiteral(f64::from_bits(i as u64)),
         (Literal::Uint64(i), &F64_TYPE) => Expression::FloatLiteral(f64::from_bits(i)),

         // Transmute float to int
         (Literal::Float32(f), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: u64::from(f.to_bits()),
            synthetic: true,
         },
         (Literal::Float64(f), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: f.to_bits(),
            synthetic: true,
         },

         // Transmute to pointer @FixedPointerWidth
         (Literal::Int32(i), &ExpressionType::Pointer(_)) => Expression::IntLiteral {
            val: u64::from(i as u32),
            synthetic: true,
         },
         (Literal::Uint32(i), &ExpressionType::Pointer(_)) => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Float32(f), &ExpressionType::Pointer(_)) => Expression::IntLiteral {
            val: u64::from(f.to_bits()),
            synthetic: true,
         },

         // Transmute signed -> unsigned
         (Literal::Int64(i), &ExpressionType::Int(it)) if !it.signed => Expression::IntLiteral {
            val: i as u64,
            synthetic: true,
         },
         (Literal::Int32(i), &ExpressionType::Int(it)) if !it.signed => Expression::IntLiteral {
            val: u64::from(i as u32),
            synthetic: true,
         },
         (Literal::Int16(i), &ExpressionType::Int(it)) if !it.signed => Expression::IntLiteral {
            val: u64::from(i as u16),
            synthetic: true,
         },
         (Literal::Int8(i), &ExpressionType::Int(it)) if !it.signed => Expression::IntLiteral {
            val: u64::from(i as u8),
            synthetic: true,
         },

         // Transmute unsigned -> signed
         (Literal::Uint64(i), &ExpressionType::Int(it)) if it.signed => Expression::IntLiteral {
            val: i,
            synthetic: true,
         },
         (Literal::Uint32(i), &ExpressionType::Int(it)) if it.signed => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Uint16(i), &ExpressionType::Int(it)) if it.signed => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Uint8(i), &ExpressionType::Int(it)) if it.signed => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },

         // Noop
         (Literal::Int64(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: i as u64,
            synthetic: true,
         },
         (Literal::Int32(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: i64::from(i) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: i64::from(i) as u64,
            synthetic: true,
         },
         (Literal::Int8(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: i64::from(i) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: i,
            synthetic: true,
         },
         (Literal::Uint32(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Uint16(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Uint8(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         _ => return None,
      })
   }

   fn do_as(self, target_type: &ExpressionType) -> Option<Expression> {
      Some(match (self, target_type) {
         (Literal::Int64(i), &ExpressionType::Int(tt)) if tt.width.as_num_bytes() >= 8 => Expression::IntLiteral {
            val: i as u64,
            synthetic: true,
         },
         (Literal::Int32(i), &ExpressionType::Int(tt)) if tt.width.as_num_bytes() >= 4 => Expression::IntLiteral {
            val: i64::from(i) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), &ExpressionType::Int(tt)) if tt.width.as_num_bytes() >= 2 => Expression::IntLiteral {
            val: i64::from(i) as u64,
            synthetic: true,
         },
         (Literal::Int8(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: i64::from(i) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), &ExpressionType::Int(tt)) if tt.width.as_num_bytes() >= 8 => Expression::IntLiteral {
            val: i,
            synthetic: true,
         },
         (Literal::Uint32(i), &ExpressionType::Int(tt)) if tt.width.as_num_bytes() >= 4 => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Uint16(i), &ExpressionType::Int(tt)) if tt.width.as_num_bytes() >= 2 => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Uint8(i), &ExpressionType::Int(_)) => Expression::IntLiteral {
            val: u64::from(i),
            synthetic: true,
         },
         (Literal::Float64(f), &F32_TYPE) => Expression::FloatLiteral(f64::from(f as f32)),
         (Literal::Float32(f), &F64_TYPE) => Expression::FloatLiteral(f64::from(f)),
         (Literal::Uint64(i), &U32_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u32),
            synthetic: true,
         },
         (Literal::Uint64(i), &U16_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u16),
            synthetic: true,
         },
         (Literal::Uint64(i), &U8_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u8),
            synthetic: true,
         },
         (Literal::Uint32(i), &U16_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u16),
            synthetic: true,
         },
         (Literal::Uint32(i), &U8_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u8),
            synthetic: true,
         },
         (Literal::Uint16(i), &U8_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u8),
            synthetic: true,
         },
         (Literal::Uint64(i), &I32_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i32) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), &I16_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i16) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), &I8_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i8) as u64,
            synthetic: true,
         },
         (Literal::Uint32(i), &I16_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i16) as u64,
            synthetic: true,
         },
         (Literal::Uint32(i), &I8_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i8) as u64,
            synthetic: true,
         },
         (Literal::Uint16(i), &I8_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i8) as u64,
            synthetic: true,
         },
         (Literal::Int64(i), &U32_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u32),
            synthetic: true,
         },
         (Literal::Int64(i), &U16_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u16),
            synthetic: true,
         },
         (Literal::Int64(i), &U8_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u8),
            synthetic: true,
         },
         (Literal::Int32(i), &U16_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u16),
            synthetic: true,
         },
         (Literal::Int32(i), &U8_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u8),
            synthetic: true,
         },
         (Literal::Int16(i), &U8_TYPE) => Expression::IntLiteral {
            val: u64::from(i as u8),
            synthetic: true,
         },
         (Literal::Int64(i), &I32_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i32) as u64,
            synthetic: true,
         },
         (Literal::Int64(i), &I16_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i16) as u64,
            synthetic: true,
         },
         (Literal::Int64(i), &I8_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i8) as u64,
            synthetic: true,
         },
         (Literal::Int32(i), &I16_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i16) as u64,
            synthetic: true,
         },
         (Literal::Int32(i), &I8_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i8) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), &I8_TYPE) => Expression::IntLiteral {
            val: i64::from(i as i8) as u64,
            synthetic: true,
         },
         _ => return None,
      })
   }

   fn checked_add(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral {
            val: i.checked_add(j)? as u64,
            synthetic: true,
         }),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_add(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_add(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_add(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral {
            val: i.checked_add(j)?,
            synthetic: true,
         }),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_add(j)?),
            synthetic: true,
         }),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_add(j)?),
            synthetic: true,
         }),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_add(j)?),
            synthetic: true,
         }),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i + j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i - j))),
         _ => unreachable!(),
      }
   }

   fn checked_sub(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral {
            val: i.checked_sub(j)? as u64,
            synthetic: true,
         }),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_sub(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_sub(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_sub(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral {
            val: i.checked_sub(j)?,
            synthetic: true,
         }),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_sub(j)?),
            synthetic: true,
         }),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_sub(j)?),
            synthetic: true,
         }),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_sub(j)?),
            synthetic: true,
         }),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i - j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i - j))),
         _ => unreachable!(),
      }
   }

   fn checked_mul(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral {
            val: i.checked_mul(j)? as u64,
            synthetic: true,
         }),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_mul(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_mul(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_mul(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral {
            val: i.checked_mul(j)?,
            synthetic: true,
         }),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_mul(j)?),
            synthetic: true,
         }),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_mul(j)?),
            synthetic: true,
         }),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_mul(j)?),
            synthetic: true,
         }),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i * j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i * j))),
         _ => unreachable!(),
      }
   }

   fn checked_rem(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral {
            val: i.checked_rem(j)? as u64,
            synthetic: true,
         }),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_rem(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_rem(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_rem(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral {
            val: i.checked_rem(j)?,
            synthetic: true,
         }),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_rem(j)?),
            synthetic: true,
         }),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_rem(j)?),
            synthetic: true,
         }),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_rem(j)?),
            synthetic: true,
         }),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i % j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i % j))),
         _ => unreachable!(),
      }
   }

   fn checked_div(self, other: Self) -> Option<Expression> {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Some(Expression::IntLiteral {
            val: i.checked_div(j)? as u64,
            synthetic: true,
         }),
         (Literal::Int32(i), Literal::Int32(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_div(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int16(i), Literal::Int16(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_div(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Int8(i), Literal::Int8(j)) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_div(j)?) as u64,
            synthetic: true,
         }),
         (Literal::Uint64(i), Literal::Uint64(j)) => Some(Expression::IntLiteral {
            val: i.checked_div(j)?,
            synthetic: true,
         }),
         (Literal::Uint32(i), Literal::Uint32(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_div(j)?),
            synthetic: true,
         }),
         (Literal::Uint16(i), Literal::Uint16(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_div(j)?),
            synthetic: true,
         }),
         (Literal::Uint8(i), Literal::Uint8(j)) => Some(Expression::IntLiteral {
            val: u64::from(i.checked_div(j)?),
            synthetic: true,
         }),
         (Literal::Float64(i), Literal::Float64(j)) => Some(Expression::FloatLiteral(i / j)),
         (Literal::Float32(i), Literal::Float32(j)) => Some(Expression::FloatLiteral(f64::from(i / j))),
         _ => unreachable!(),
      }
   }

   fn checked_shl(self, rhs: Self) -> Option<Expression> {
      Some(match (self, rhs) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral {
            val: (i.checked_shl(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral {
            val: i64::from(i.checked_shl(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral {
            val: i64::from(i.checked_shl(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral {
            val: i64::from(i.checked_shl(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral {
            val: i.checked_shl(j.try_into().ok()?)?,
            synthetic: true,
         },
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral {
            val: u64::from(i.checked_shl(j)?),
            synthetic: true,
         },
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral {
            val: u64::from(i.checked_shl(u32::from(j))?),
            synthetic: true,
         },
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral {
            val: u64::from(i.checked_shl(u32::from(j))?),
            synthetic: true,
         },
         _ => unreachable!(),
      })
   }

   fn checked_shr(self, rhs: Self) -> Option<Expression> {
      Some(match (self, rhs) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral {
            val: (i.checked_shr(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral {
            val: i64::from(i.checked_shr(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral {
            val: i64::from(i.checked_shr(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral {
            val: i64::from(i.checked_shr(j.try_into().ok()?)?) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral {
            val: i.checked_shr(j.try_into().ok()?)?,
            synthetic: true,
         },
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral {
            val: u64::from(i.checked_shr(j)?),
            synthetic: true,
         },
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral {
            val: u64::from(i.checked_shr(u32::from(j))?),
            synthetic: true,
         },
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral {
            val: u64::from(i.checked_shr(u32::from(j))?),
            synthetic: true,
         },
         _ => unreachable!(),
      })
   }

   fn checked_negate(self) -> Option<Expression> {
      match self {
         Literal::Int64(i) => Some(Expression::IntLiteral {
            val: i.checked_neg()? as u64,
            synthetic: true,
         }),
         Literal::Int32(i) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_neg()?) as u64,
            synthetic: true,
         }),
         Literal::Int16(i) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_neg()?) as u64,
            synthetic: true,
         }),
         Literal::Int8(i) => Some(Expression::IntLiteral {
            val: i64::from(i.checked_neg()?) as u64,
            synthetic: true,
         }),
         Literal::Float64(i) => Some(Expression::FloatLiteral(-i)),
         Literal::Float32(i) => Some(Expression::FloatLiteral(f64::from(-i))),
         _ => unreachable!(),
      }
   }

   fn complement(self) -> Expression {
      match self {
         Literal::Int64(i) => Expression::IntLiteral {
            val: (!i) as u64,
            synthetic: true,
         },
         Literal::Int32(i) => Expression::IntLiteral {
            val: i64::from(!i) as u64,
            synthetic: true,
         },
         Literal::Int16(i) => Expression::IntLiteral {
            val: i64::from(!i) as u64,
            synthetic: true,
         },
         Literal::Int8(i) => Expression::IntLiteral {
            val: i64::from(!i) as u64,
            synthetic: true,
         },
         Literal::Uint64(i) => Expression::IntLiteral {
            val: !i,
            synthetic: true,
         },
         Literal::Uint32(i) => Expression::IntLiteral {
            val: u64::from(!i),
            synthetic: true,
         },
         Literal::Uint16(i) => Expression::IntLiteral {
            val: u64::from(!i),
            synthetic: true,
         },
         Literal::Uint8(i) => Expression::IntLiteral {
            val: u64::from(!i),
            synthetic: true,
         },
         Literal::Bool(b) => Expression::BoolLiteral(!b),
         _ => unreachable!(),
      }
   }
}

impl BitXor for Literal {
   type Output = Expression;

   fn bitxor(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral {
            val: (i ^ j) as u64,
            synthetic: true,
         },
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral {
            val: i64::from(i ^ j) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral {
            val: i64::from(i ^ j) as u64,
            synthetic: true,
         },
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral {
            val: i64::from(i ^ j) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral {
            val: i ^ j,
            synthetic: true,
         },
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral {
            val: u64::from(i ^ j),
            synthetic: true,
         },
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral {
            val: u64::from(i ^ j),
            synthetic: true,
         },
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral {
            val: u64::from(i ^ j),
            synthetic: true,
         },
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i ^ j),
         _ => unreachable!(),
      }
   }
}

impl BitOr for Literal {
   type Output = Expression;

   fn bitor(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral {
            val: (i | j) as u64,
            synthetic: true,
         },
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral {
            val: i64::from(i | j) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral {
            val: i64::from(i | j) as u64,
            synthetic: true,
         },
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral {
            val: i64::from(i | j) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral {
            val: i | j,
            synthetic: true,
         },
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral {
            val: u64::from(i | j),
            synthetic: true,
         },
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral {
            val: u64::from(i | j),
            synthetic: true,
         },
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral {
            val: u64::from(i | j),
            synthetic: true,
         },
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i | j),
         _ => unreachable!(),
      }
   }
}

impl BitAnd for Literal {
   type Output = Expression;

   fn bitand(self, other: Self) -> Self::Output {
      match (self, other) {
         (Literal::Int64(i), Literal::Int64(j)) => Expression::IntLiteral {
            val: (i & j) as u64,
            synthetic: true,
         },
         (Literal::Int32(i), Literal::Int32(j)) => Expression::IntLiteral {
            val: i64::from(i & j) as u64,
            synthetic: true,
         },
         (Literal::Int16(i), Literal::Int16(j)) => Expression::IntLiteral {
            val: i64::from(i & j) as u64,
            synthetic: true,
         },
         (Literal::Int8(i), Literal::Int8(j)) => Expression::IntLiteral {
            val: i64::from(i & j) as u64,
            synthetic: true,
         },
         (Literal::Uint64(i), Literal::Uint64(j)) => Expression::IntLiteral {
            val: i & j,
            synthetic: true,
         },
         (Literal::Uint32(i), Literal::Uint32(j)) => Expression::IntLiteral {
            val: u64::from(i & j),
            synthetic: true,
         },
         (Literal::Uint16(i), Literal::Uint16(j)) => Expression::IntLiteral {
            val: u64::from(i & j),
            synthetic: true,
         },
         (Literal::Uint8(i), Literal::Uint8(j)) => Expression::IntLiteral {
            val: u64::from(i & j),
            synthetic: true,
         },
         (Literal::Bool(i), Literal::Bool(j)) => Expression::BoolLiteral(i & j),
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
   match &expr_node.expression {
      Expression::IntLiteral { val: x, .. } => {
         let x = *x;
         match expr_node.exp_type.as_ref().unwrap() {
            &I64_TYPE => Some(Literal::Int64(x as i64)),
            &I32_TYPE => Some(Literal::Int32((x as i64).try_into().ok()?)),
            &I16_TYPE => Some(Literal::Int16((x as i64).try_into().ok()?)),
            &I8_TYPE => Some(Literal::Int8((x as i64).try_into().ok()?)),
            // @FixedPointerWidth
            &ISIZE_TYPE => Some(Literal::Int32(x.try_into().ok()?)),
            &U64_TYPE => Some(Literal::Uint64(x)),
            &U32_TYPE => Some(Literal::Uint32(x.try_into().ok()?)),
            &U16_TYPE => Some(Literal::Uint16(x.try_into().ok()?)),
            &U8_TYPE => Some(Literal::Uint8(x.try_into().ok()?)),
            // @FixedPointerWidth
            &USIZE_TYPE => Some(Literal::Uint32(x.try_into().ok()?)),
            // @FixedPointerWidth
            ExpressionType::Pointer(_) => Some(Literal::Uint32(x.try_into().ok()?)),
            _ => unreachable!(),
         }
      }
      Expression::FloatLiteral(x) => match *expr_node.exp_type.as_ref().unwrap() {
         F64_TYPE => Some(Literal::Float64(*x)),
         F32_TYPE => Some(Literal::Float32(*x as f32)),
         _ => unreachable!(),
      },
      Expression::BoolLiteral(x) => Some(Literal::Bool(*x)),
      Expression::EnumLiteral(x, y) => Some(Literal::Enum(*x, y.str)),
      Expression::UnitLiteral => Some(Literal::Unit),
      _ => None,
   }
}

fn is_commutative_noop(literal: Literal, op: BinOp) -> bool {
   (literal.is_int_one() & (op == BinOp::Multiply))
      || (literal.is_int_zero() & (op == BinOp::Add))
      || (literal.is_int_zero() & (op == BinOp::BitwiseOr))
      || (literal.is_int_max() & (op == BinOp::BitwiseAnd))
      || ((literal == Literal::Bool(false)) & (op == BinOp::BitwiseOr))
      || ((literal == Literal::Bool(true)) & (op == BinOp::BitwiseAnd))
      || ((literal == Literal::Bool(false)) & (op == BinOp::LogicalOr))
      || ((literal == Literal::Bool(true)) & (op == BinOp::LogicalAnd))
}

pub fn expression_could_have_side_effects(expr_id: ExpressionId, expressions: &ExpressionPool) -> bool {
   match &expressions[expr_id].expression {
      Expression::ProcedureCall { .. } => true, // @PureCalls
      Expression::ArrayLiteral(arr) => arr.iter().any(|x| expression_could_have_side_effects(*x, expressions)),
      Expression::ArrayIndex { array, index } => {
         expression_could_have_side_effects(*array, expressions)
            || expression_could_have_side_effects(*index, expressions)
      }
      Expression::BinaryOperator { lhs, rhs, .. } => {
         expression_could_have_side_effects(*lhs, expressions) || expression_could_have_side_effects(*rhs, expressions)
      }
      Expression::UnaryOperator(_, expr) => expression_could_have_side_effects(*expr, expressions),
      Expression::StructLiteral(_, fields) => fields
         .iter()
         .flat_map(|(_, x)| x)
         .any(|x| expression_could_have_side_effects(*x, expressions)),
      Expression::FieldAccess(_, expr) => expression_could_have_side_effects(*expr, expressions),
      Expression::Cast { expr, .. } => expression_could_have_side_effects(*expr, expressions),
      Expression::IfX(a, b, c) => {
         expression_could_have_side_effects(*a, expressions)
            || expression_could_have_side_effects(*b, expressions)
            || expression_could_have_side_effects(*c, expressions)
      }
      Expression::EnumLiteral(_, _) => false,
      Expression::BoolLiteral(_) => false,
      Expression::StringLiteral(_) => false,
      Expression::IntLiteral { .. } => false,
      Expression::FloatLiteral(_) => false,
      Expression::UnitLiteral | Expression::BoundFcnLiteral(_, _) => false,
      Expression::Variable(_) => false,
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
}
