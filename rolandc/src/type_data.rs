use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::HashMap;

use crate::interner::{Interner, StrId};
use crate::semantic_analysis::type_variables::{TypeConstraint, TypeVariable, TypeVariableManager};
use crate::size_info::SizeInfo;

pub const U8_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: false,
   width: IntWidth::One,
});

pub const U16_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: false,
   width: IntWidth::Two,
});

pub const U32_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: false,
   width: IntWidth::Four,
});

pub const U64_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: false,
   width: IntWidth::Eight,
});

pub const USIZE_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: false,
   width: IntWidth::Pointer,
});

pub const I8_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: true,
   width: IntWidth::One,
});

pub const I16_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: true,
   width: IntWidth::Two,
});

pub const I32_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: true,
   width: IntWidth::Four,
});

pub const I64_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: true,
   width: IntWidth::Eight,
});

pub const ISIZE_TYPE: ExpressionType = ExpressionType::Int(IntType {
   signed: true,
   width: IntWidth::Pointer,
});

pub const F32_TYPE: ExpressionType = ExpressionType::Float(FloatType {
   width: FloatWidth::Four,
});

pub const F64_TYPE: ExpressionType = ExpressionType::Float(FloatType {
   width: FloatWidth::Eight,
});

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExpressionType {
   Unknown(TypeVariable),
   Int(IntType),
   Float(FloatType),
   Bool,
   Unit,
   Struct(StrId),
   Array(Box<ExpressionType>, u32),
   Pointer(Box<ExpressionType>),
   CompileError,
   Enum(StrId),
   ProcedureItem(StrId, Box<[ExpressionType]>),
   ProcedurePointer {
      parameters: Box<[ExpressionType]>,
      ret_type: Box<ExpressionType>,
   },
   Unresolved(StrId), // Could be a struct, enum, generic parameter, or fail to resolve (compilation error)
   Never,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FloatWidth {
   Eight,
   Four,
}

impl FloatWidth {
   #[must_use]
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
   #[must_use]
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
   pub fn decrement_indirection_count(&mut self) -> Result<(), ()> {
      match self {
         ExpressionType::Pointer(v) => {
            let mut inner_value = ExpressionType::Unit;
            std::mem::swap(&mut **v, &mut inner_value);
            *self = inner_value;
            Ok(())
         }
         _ => Err(()),
      }
   }

   #[must_use]
   pub fn get_type_or_type_being_pointed_to(&self) -> &ExpressionType {
      match self {
         ExpressionType::Pointer(b) => b,
         _ => self,
      }
   }

   #[must_use]
   pub fn get_type_variable_of_unknown_type(&self) -> Option<TypeVariable> {
      match self {
         ExpressionType::Unknown(x) => Some(*x),
         ExpressionType::Pointer(v) => v.get_type_variable_of_unknown_type(),
         ExpressionType::Array(v, _) => v.get_type_variable_of_unknown_type(),
         // other types can't contain unknown values, at least right now
         _ => None,
      }
   }

   #[must_use]
   pub fn get_unknown_portion_of_type(&mut self) -> Option<&mut ExpressionType> {
      match self {
         x @ ExpressionType::Unknown(_) => Some(x),
         ExpressionType::Pointer(x) => x.get_unknown_portion_of_type(),
         ExpressionType::Array(v, _) => v.get_unknown_portion_of_type(),
         _ => None,
      }
   }

   #[must_use]
   pub fn is_concrete(&self) -> bool {
      match self {
         ExpressionType::Unknown(_) | ExpressionType::CompileError | ExpressionType::Unresolved(_) => false,
         ExpressionType::Int(_)
         | ExpressionType::Float(_)
         | ExpressionType::Bool
         | ExpressionType::Unit
         | ExpressionType::Never
         | ExpressionType::Struct(_)
         | ExpressionType::ProcedureItem(_, _)
         | ExpressionType::ProcedurePointer { .. }
         | ExpressionType::Enum(_) => true,
         ExpressionType::Array(exp, _) => exp.is_concrete(),
         ExpressionType::Pointer(exp) => exp.is_concrete(),
      }
   }

   #[must_use]
   pub fn is_error(&self) -> bool {
      match self {
         ExpressionType::CompileError => true,
         ExpressionType::Array(exp, _) => exp.is_error(),
         ExpressionType::Pointer(exp) => exp.is_error(),
         _ => false,
      }
   }

   #[must_use]
   pub fn is_pointer(&self) -> bool {
      matches!(self, ExpressionType::Pointer(_))
   }

   #[must_use]
   pub fn is_never(&self) -> bool {
      matches!(self, ExpressionType::Never)
   }

   #[must_use]
   pub fn is_or_contains_never(&self, struct_size_info: &HashMap<StrId, SizeInfo>) -> bool {
      match self {
         ExpressionType::Never => true,
         ExpressionType::Struct(s) => struct_size_info.get(s).unwrap().contains_never_type,
         ExpressionType::Array(inner_t, _) => inner_t.is_or_contains_never(struct_size_info),
         ExpressionType::Pointer(inner_t) => inner_t.is_or_contains_never(struct_size_info),
         _ => false,
      }
   }

   #[must_use]
   pub fn as_roland_type_info<'i>(
      &self,
      interner: &'i Interner,
      type_variable_info: &TypeVariableManager,
   ) -> Cow<'i, str> {
      self.as_roland_type_info_inner(interner, Some(type_variable_info))
   }

   #[must_use]
   fn as_roland_type_info_inner<'i>(
      &self,
      interner: &'i Interner,
      type_variable_info: Option<&TypeVariableManager>,
   ) -> Cow<'i, str> {
      match self {
         ExpressionType::Unknown(x) => {
            if let Some(tvi) = type_variable_info {
               match tvi.get_data(*x).constraint {
                  TypeConstraint::Int => Cow::Borrowed("?? Int"),
                  TypeConstraint::SignedInt => Cow::Borrowed("?? Signed Int"),
                  TypeConstraint::Float => Cow::Borrowed("?? Float"),
                  TypeConstraint::None => Cow::Borrowed("??"),
               }
            } else {
               Cow::Borrowed("??")
            }
         }
         ExpressionType::Int(x) => match (x.signed, &x.width) {
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
         ExpressionType::Float(x) => match x.width {
            FloatWidth::Eight => Cow::Borrowed("f64"),
            FloatWidth::Four => Cow::Borrowed("f32"),
         },
         ExpressionType::Bool => Cow::Borrowed("bool"),
         ExpressionType::Unit => Cow::Borrowed("()"),
         ExpressionType::Never => Cow::Borrowed("!"),
         ExpressionType::CompileError => Cow::Borrowed("ERROR"),
         ExpressionType::Struct(x) if interner.reverse_lookup("String").map_or(false, |sid| sid == *x) => {
            Cow::Borrowed("String")
         }
         ExpressionType::Struct(x) => Cow::Owned(format!("Struct {}", interner.lookup(*x))),
         ExpressionType::Enum(x) => Cow::Owned(format!("Enum {}", interner.lookup(*x))),
         ExpressionType::Array(i_type, length) => Cow::Owned(format!(
            "[{}; {}]",
            i_type.as_roland_type_info_inner(interner, type_variable_info),
            length
         )),
         ExpressionType::Pointer(i_type) => Cow::Owned(format!(
            "&{}",
            i_type.as_roland_type_info_inner(interner, type_variable_info)
         )),
         ExpressionType::Unresolved(x) => Cow::Borrowed(interner.lookup(*x)),
         ExpressionType::ProcedurePointer {
            parameters,
            ret_type: ret_val,
         } => {
            let params: String = parameters
               .iter()
               .map(|x| x.as_roland_type_info_inner(interner, type_variable_info))
               .collect::<Vec<_>>()
               .join(", ");
            Cow::Owned(format!(
               "proc({}) -> {}",
               params,
               ret_val.as_roland_type_info_inner(interner, type_variable_info)
            ))
         }
         ExpressionType::ProcedureItem(proc_name, type_arguments) => {
            if type_arguments.is_empty() {
               Cow::Owned(format!("proc() {{{}}}", interner.lookup(*proc_name),))
            } else {
               let type_argument_string = type_arguments
                  .iter()
                  .map(|x| x.as_roland_type_info_like_source(interner))
                  .collect::<Vec<_>>()
                  .join("$");
               Cow::Owned(format!(
                  "proc() {{{}${}}}",
                  interner.lookup(*proc_name),
                  type_argument_string
               ))
            }
         }
      }
   }

   #[must_use]
   pub fn as_roland_type_info_notv<'i>(&self, interner: &'i Interner) -> Cow<'i, str> {
      self.as_roland_type_info_inner(interner, None)
   }

   #[must_use]
   pub fn as_roland_type_info_like_source<'i>(&self, interner: &'i Interner) -> Cow<'i, str> {
      match self {
         ExpressionType::Unknown(_) => unreachable!(),
         ExpressionType::Int(x) => match (x.signed, &x.width) {
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
         ExpressionType::Float(x) => match x.width {
            FloatWidth::Eight => Cow::Borrowed("f64"),
            FloatWidth::Four => Cow::Borrowed("f32"),
         },
         ExpressionType::Bool => Cow::Borrowed("bool"),
         ExpressionType::Unit => Cow::Borrowed("()"),
         ExpressionType::Never => Cow::Borrowed("!"),
         ExpressionType::CompileError => Cow::Borrowed("ERROR"),
         ExpressionType::Struct(x) => Cow::Borrowed(interner.lookup(*x)),
         ExpressionType::Enum(x) => Cow::Borrowed(interner.lookup(*x)),
         ExpressionType::Array(i_type, length) => Cow::Owned(format!(
            "[{}; {}]",
            i_type.as_roland_type_info_like_source(interner),
            length
         )),
         ExpressionType::Pointer(i_type) => Cow::Owned(format!("&{}", i_type.as_roland_type_info_notv(interner))),
         ExpressionType::Unresolved(x) => Cow::Borrowed(interner.lookup(*x)),
         ExpressionType::ProcedurePointer {
            parameters,
            ret_type: ret_val,
         } => {
            let params: String = parameters
               .iter()
               .map(|x| x.as_roland_type_info_like_source(interner))
               .collect::<Vec<_>>()
               .join(", ");
            Cow::Owned(format!(
               "proc({}) -> {}",
               params,
               ret_val.as_roland_type_info_like_source(interner)
            ))
         }
         ExpressionType::ProcedureItem(_, _) => unreachable!(),
      }
   }
}
