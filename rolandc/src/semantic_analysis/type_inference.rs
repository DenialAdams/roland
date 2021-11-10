use std::io::Write;

use super::ValidationContext;
use crate::interner::Interner;
use crate::parse::{Expression, ExpressionNode, UnOp};
use crate::type_data::{ExpressionType, I16_TYPE, I32_TYPE, I64_TYPE, I8_TYPE, ISIZE_TYPE, IntType, U16_TYPE, U32_TYPE, U64_TYPE, U8_TYPE, USIZE_TYPE, ValueType};

// Returns false if the types being inferred are incompatible
// Inference may still not be possible for other reasons
fn inference_is_impossible(source_type: &ExpressionType, target_type: &ExpressionType) -> bool {
   match source_type {
      ExpressionType::Value(ValueType::Array(src_e, _)) => match target_type {
         ExpressionType::Value(ValueType::Array(target_e, _)) => inference_is_impossible(src_e, target_e),
         _ => true,
      },
      ExpressionType::Value(ValueType::UnknownFloat) => !target_type.is_any_known_float(),
      ExpressionType::Value(ValueType::UnknownInt) => !target_type.is_any_known_int(),
      _ => true,
   }
}

pub fn try_set_inferred_type<W: Write>(
   e_type: &ExpressionType,
   expr_node: &mut ExpressionNode,
   validation_context: &mut ValidationContext,
   err_stream: &mut W,
   interner: &mut Interner,
) {
   let source_type = expr_node.exp_type.as_ref().unwrap();
   if inference_is_impossible(source_type, e_type) {
      return;
   }

   set_inferred_type(e_type, expr_node, validation_context, err_stream, interner)
}

fn set_inferred_type<W: Write>(
   e_type: &ExpressionType,
   expr_node: &mut ExpressionNode,
   validation_context: &mut ValidationContext,
   err_stream: &mut W,
   interner: &mut Interner,
) {
   match &mut expr_node.expression {
      Expression::Extend(_, _) => unreachable!(),
      Expression::Truncate(_, _) => unreachable!(),
      Expression::Transmute(_, _) => unreachable!(),
      Expression::BoolLiteral(_) => unreachable!(),
      Expression::IntLiteral(val) => {
         validation_context.unknown_ints -= 1;
         let overflowing_literal = match &e_type {
            ExpressionType::Value(I8_TYPE) => *val > i64::from(i8::MAX) || *val < i64::from(i8::MIN),
            ExpressionType::Value(I16_TYPE) => *val > i64::from(i16::MAX) || *val < i64::from(i16::MIN),
            ExpressionType::Value(I32_TYPE) => *val > i64::from(i32::MAX) || *val < i64::from(i32::MIN),
            // @FixedPointerWidth
            ExpressionType::Value(ISIZE_TYPE) => *val > i64::from(i32::MAX) || *val < i64::from(i32::MIN),
            // TODO: add checking for i64 type (currently doesn't make sense because we lex literals as i64 instead of i128 or larger)
            ExpressionType::Value(I64_TYPE) => false,
            ExpressionType::Value(U8_TYPE) => *val > i64::from(u8::MAX) || *val < i64::from(u8::MIN),
            ExpressionType::Value(U16_TYPE) => *val > i64::from(u16::MAX) || *val < i64::from(u16::MIN),
            ExpressionType::Value(U32_TYPE) => *val > i64::from(u32::MAX) || *val < i64::from(u32::MIN),
            // @FixedPointerWidth
            ExpressionType::Value(USIZE_TYPE) => *val > i64::from(u32::MAX) || *val < i64::from(u32::MIN),
            // TODO: add checking for overflow of u64 type (currently impossible pending lexer)
            ExpressionType::Value(U64_TYPE) => *val < 0,
            _ => unreachable!(),
         };
         if overflowing_literal {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Literal of type {} has value `{}` which would immediately over/underflow",
               e_type.as_roland_type_info(interner),
               val
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
            )
            .unwrap();
         }
         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::FloatLiteral(_) => {
         validation_context.unknown_floats -= 1;
         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::StringLiteral(_) => unreachable!(),
      Expression::BinaryOperator(_, e) => {
         set_inferred_type(e_type, &mut e.0, validation_context, err_stream, interner);
         set_inferred_type(e_type, &mut e.1, validation_context, err_stream, interner);
         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::UnaryOperator(unop, e) => {
         set_inferred_type(e_type, e, validation_context, err_stream, interner);

         if *unop == UnOp::Negate && matches!(e.exp_type, Some(ExpressionType::Value(ValueType::Int(IntType { signed: false, ..})))) {
            validation_context.error_count += 1;
            writeln!(
               err_stream,
               "Unsigned integers (i.e. {}) can't be negated. Hint: Should this be a signed integer?",
               e_type.as_roland_type_info(interner),
            )
            .unwrap();
            writeln!(
               err_stream,
               "↳ line {}, column {}",
               expr_node.expression_begin_location.line, expr_node.expression_begin_location.col
            )
            .unwrap();
         }

         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::UnitLiteral => unreachable!(),
      Expression::Variable(_) => (),
      Expression::ProcedureCall(_, _) => unreachable!(),
      Expression::StructLiteral(_, _) => unreachable!(),
      Expression::FieldAccess(_, _) => unreachable!(),
      Expression::ArrayLiteral(exprs) => {
         let target_elem_type = match e_type {
            ExpressionType::Value(ValueType::Array(inner_type, _)) => inner_type,
            _ => unreachable!(),
         };

         for expr in exprs.iter_mut() {
            set_inferred_type(target_elem_type, expr, validation_context, err_stream, interner);
         }

         // It's important that we don't override the length here; that can't be inferred
         match &mut expr_node.exp_type {
            Some(ExpressionType::Value(ValueType::Array(a_type, _))) => *a_type = target_elem_type.clone(),
            _ => unreachable!(),
         }
      }
      Expression::ArrayIndex(array_expr, _index_expr) => {
         // The length is bogus, but we don't care about that during inference anyway
         let array_type = ExpressionType::Value(ValueType::Array(Box::new(e_type.clone()), 0));
         set_inferred_type(&array_type, array_expr, validation_context, err_stream, interner);
         expr_node.exp_type = Some(e_type.clone());
      }
      Expression::EnumLiteral(_, _) => unreachable!(),
   }
}
