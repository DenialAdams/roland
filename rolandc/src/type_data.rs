use std::borrow::Cow;

pub const U8_TYPE: ValueType = ValueType::Int(IntType {
   signed: false,
   width: IntWidth::One,
});

pub const U16_TYPE: ValueType = ValueType::Int(IntType {
   signed: false,
   width: IntWidth::Two,
});

pub const U32_TYPE: ValueType = ValueType::Int(IntType {
   signed: false,
   width: IntWidth::Four,
});

pub const U64_TYPE: ValueType = ValueType::Int(IntType {
   signed: false,
   width: IntWidth::Eight,
});

pub const I8_TYPE: ValueType = ValueType::Int(IntType {
   signed: true,
   width: IntWidth::One,
});

pub const I16_TYPE: ValueType = ValueType::Int(IntType {
   signed: true,
   width: IntWidth::Two,
});

pub const I32_TYPE: ValueType = ValueType::Int(IntType {
   signed: true,
   width: IntWidth::Four,
});

pub const I64_TYPE: ValueType = ValueType::Int(IntType {
   signed: true,
   width: IntWidth::Eight,
});

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpressionType {
   Value(ValueType),
   Pointer(usize, ValueType),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueType {
   UnknownInt,
   Int(IntType),
   String,
   Bool,
   Unit,
   Struct(String),
   CompileError,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntWidth {
   Eight,
   Four,
   Two,
   One,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntType {
   pub signed: bool,
   pub width: IntWidth,
}

impl ExpressionType {
   pub fn is_compound_type(&self) -> bool {
      match self {
         ExpressionType::Value(x) => x.is_compound_type(),
         ExpressionType::Pointer(_, x) => false,
      }
   }

   pub fn is_concrete_type(&self) -> bool {
      match self {
         ExpressionType::Value(x) => x.is_concrete_type(),
         ExpressionType::Pointer(_, x) => x.is_concrete_type(),
      }
   }

   pub fn is_any_known_int(&self) -> bool {
      match self {
         ExpressionType::Value(ValueType::Int(_)) => true,
         _ => false,
      }
   }

   pub fn as_roland_type_info(&self) -> String {
      match self {
         ExpressionType::Value(x) => x.as_roland_type_info().into(),
         ExpressionType::Pointer(x, y) => {
            let base_type = y.as_roland_type_info();
            let mut s: String = String::with_capacity(x + base_type.len());
            for _ in 0..*x {
               s.push('&');
            }
            s.push_str(&*base_type);
            s
         }
      }
   }

   pub fn increment_indirection_count(&mut self) {
      match self {
         ExpressionType::Value(v) => {
            // UGH this clone is so un-necessary, i don't know how to fix safely
            // TODO
            *self = ExpressionType::Pointer(1, v.clone());
         }
         ExpressionType::Pointer(i, _) => {
            *i += 1;
         }
      }
   }

   pub fn decrement_indirection_count(&mut self) -> Result<(), ()> {
      match self {
         ExpressionType::Value(_) => Err(()),
         ExpressionType::Pointer(1, v) => {
            // UGH this clone is so un-necessary, i don't know how to fix safely
            // TODO
            *self = ExpressionType::Value(v.clone());
            Ok(())
         }
         ExpressionType::Pointer(i, _) => {
            *i -= 1;
            Ok(())
         }
      }
   }
}

impl ValueType {
   fn is_compound_type(&self) -> bool {
      match self {
         ValueType::Struct(_) | ValueType::String => true,
         ValueType::Int(_) | ValueType::Bool | ValueType::Unit | ValueType::UnknownInt | ValueType::CompileError => false,
      }
   }

   fn is_concrete_type(&self) -> bool {
      match self {
         ValueType::UnknownInt | ValueType::CompileError => false,
         ValueType::Int(_) | ValueType::String | ValueType::Bool | ValueType::Unit | ValueType::Struct(_) => true,
      }
   }

   fn as_roland_type_info(&self) -> Cow<str> {
      match self {
         ValueType::UnknownInt => Cow::Borrowed("?? Int"),
         ValueType::Int(x) => match (x.signed, &x.width) {
            (true, IntWidth::Eight) => Cow::Borrowed("i64"),
            (true, IntWidth::Four) => Cow::Borrowed("i32"),
            (true, IntWidth::Two) => Cow::Borrowed("i16"),
            (true, IntWidth::One) => Cow::Borrowed("i8"),
            (false, IntWidth::Eight) => Cow::Borrowed("u64"),
            (false, IntWidth::Four) => Cow::Borrowed("u32"),
            (false, IntWidth::Two) => Cow::Borrowed("u16"),
            (false, IntWidth::One) => Cow::Borrowed("u8"),
         },
         ValueType::String => Cow::Borrowed("String"),
         ValueType::Bool => Cow::Borrowed("bool"),
         ValueType::Unit => Cow::Borrowed("()"),
         ValueType::CompileError => Cow::Borrowed("ERROR"),
         ValueType::Struct(x) => Cow::Owned(format!("Struct {}", x)),
      }
   }
}
