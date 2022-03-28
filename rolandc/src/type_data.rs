use std::borrow::Cow;
use std::cmp::Ordering;

use crate::interner::{Interner, StrId};

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

pub const USIZE_TYPE: ValueType = ValueType::Int(IntType {
   signed: false,
   width: IntWidth::Pointer,
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

pub const ISIZE_TYPE: ValueType = ValueType::Int(IntType {
   signed: true,
   width: IntWidth::Pointer,
});

pub const F32_TYPE: ValueType = ValueType::Float(FloatType {
   width: FloatWidth::Four,
});

pub const F64_TYPE: ValueType = ValueType::Float(FloatType {
   width: FloatWidth::Eight,
});

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExpressionType {
   Value(ValueType),
   Pointer(usize, ValueType),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValueType {
   UnknownInt,
   UnknownFloat,
   Int(IntType),
   Float(FloatType),
   Bool,
   Unit,
   Struct(StrId),
   Array(Box<ExpressionType>, i128),
   CompileError,
   Enum(StrId),
   Unresolved(StrId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FloatWidth {
   Eight,
   Four,
}

impl FloatWidth {
   pub fn as_num_bytes(self) -> u8 {
      match self {
         FloatWidth::Eight => 8,
         FloatWidth::Four => 4,
      }
   }
}

impl PartialOrd for FloatWidth {
   fn partial_cmp(&self, other: &FloatWidth) -> Option<Ordering> {
      Some(self.cmp(other))
   }
}

impl Ord for FloatWidth {
   fn cmp(&self, other: &FloatWidth) -> Ordering {
      self.as_num_bytes().cmp(&other.as_num_bytes())
   }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntWidth {
   Pointer,
   Eight,
   Four,
   Two,
   One,
}

impl IntWidth {
   pub fn as_num_bytes(self) -> u8 {
      match self {
         IntWidth::Eight => 8,
         // @FixedPointerWidth
         IntWidth::Four | IntWidth::Pointer => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      }
   }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntType {
   pub signed: bool,
   pub width: IntWidth,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FloatType {
   pub width: FloatWidth,
}

impl ExpressionType {
   pub fn is_concrete_type(&self) -> bool {
      match self {
         ExpressionType::Value(x) => x.is_concrete_type(),
         ExpressionType::Pointer(_, x) => x.is_concrete_type(),
      }
   }

   pub fn is_error_type(&self) -> bool {
      match self {
         ExpressionType::Value(x) => x.is_error_type(),
         ExpressionType::Pointer(_, x) => x.is_error_type(),
      }
   }

   pub fn is_any_known_int(&self) -> bool {
      matches!(self, ExpressionType::Value(ValueType::Int(_)))
   }

   pub fn is_any_known_float(&self) -> bool {
      matches!(self, ExpressionType::Value(ValueType::Float(_)))
   }

   pub fn is_pointer(&self) -> bool {
      matches!(self, ExpressionType::Pointer(_, _))
   }

   pub fn as_roland_type_info(&self, interner: &mut Interner) -> String {
      match self {
         ExpressionType::Value(x) => x.as_roland_type_info(interner).into(),
         ExpressionType::Pointer(x, y) => {
            let base_type = y.as_roland_type_info(interner);
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
            // bool is just a dummy type here
            let inner_value = std::mem::replace(v, ValueType::Bool);
            *self = ExpressionType::Pointer(1, inner_value);
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
            // bool is just a dummy type here
            let inner_value = std::mem::replace(v, ValueType::Bool);
            *self = ExpressionType::Value(inner_value);
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
   fn is_concrete_type(&self) -> bool {
      match self {
         ValueType::UnknownInt | ValueType::UnknownFloat | ValueType::CompileError | ValueType::Unresolved(_) => false,
         ValueType::Int(_)
         | ValueType::Float(_)
         | ValueType::Bool
         | ValueType::Unit
         | ValueType::Struct(_)
         | ValueType::Enum(_) => true,
         ValueType::Array(exp, _) => exp.is_concrete_type(),
      }
   }

   fn is_error_type(&self) -> bool {
      match self {
         ValueType::CompileError => true,
         ValueType::Array(exp, _) => exp.is_error_type(),
         _ => false,
      }
   }

   fn as_roland_type_info<'i>(&self, interner: &'i mut Interner) -> Cow<'i, str> {
      match self {
         ValueType::UnknownFloat => Cow::Borrowed("?? Float"),
         ValueType::UnknownInt => Cow::Borrowed("?? Int"),
         ValueType::Int(x) => match (x.signed, &x.width) {
            (true, IntWidth::Pointer) => Cow::Borrowed("isize"),
            (true, IntWidth::Eight) => Cow::Borrowed("i64"),
            (true, IntWidth::Four) => Cow::Borrowed("i32"),
            (true, IntWidth::Two) => Cow::Borrowed("i16"),
            (true, IntWidth::One) => Cow::Borrowed("i8"),
            (false, IntWidth::Pointer) => Cow::Borrowed("usize"),
            (false, IntWidth::Eight) => Cow::Borrowed("u64"),
            (false, IntWidth::Four) => Cow::Borrowed("u32"),
            (false, IntWidth::Two) => Cow::Borrowed("u16"),
            (false, IntWidth::One) => Cow::Borrowed("u8"),
         },
         ValueType::Float(x) => match x.width {
            FloatWidth::Eight => Cow::Borrowed("f64"),
            FloatWidth::Four => Cow::Borrowed("f32"),
         },
         ValueType::Bool => Cow::Borrowed("bool"),
         ValueType::Unit => Cow::Borrowed("()"),
         ValueType::CompileError => Cow::Borrowed("ERROR"),
         ValueType::Struct(x) if *x == interner.intern("String") => Cow::Borrowed("String"),
         ValueType::Struct(x) => Cow::Owned(format!("Struct {}", interner.lookup(*x))),
         ValueType::Enum(x) => Cow::Owned(format!("Enum {}", interner.lookup(*x))),
         ValueType::Array(i_type, length) => {
            Cow::Owned(format!("[{}; {}]", i_type.as_roland_type_info(interner), length))
         }
         ValueType::Unresolved(x) => Cow::Borrowed(interner.lookup(*x)),
      }
   }
}
