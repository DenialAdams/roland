use std::borrow::Cow;
use std::cmp::Ordering;

use slotmap::SlotMap;

use crate::Target;
use crate::interner::{Interner, StrId};
use crate::parse::{EnumId, ProcedureId, ProcedureNode, StructId, UnionId, UserDefinedTypeInfo};
use crate::semantic_analysis::type_variables::{TypeConstraint, TypeVariable, TypeVariableManager};

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
   Struct(StructId, Box<[ExpressionType]>),
   Union(UnionId, Box<[ExpressionType]>),
   Array(Box<ExpressionType>, u32),
   Pointer(Box<ExpressionType>),
   CompileError,
   Enum(EnumId),
   ProcedureItem(ProcedureId, Box<[ExpressionType]>),
   ProcedurePointer {
      parameters: Box<[ExpressionType]>,
      ret_type: Box<ExpressionType>,
   },
   GenericParam(StrId),
   Unresolved {
      name: StrId,
      generic_args: Box<[ExpressionType]>,
   }, // Could be a struct, enum, generic parameter, or fail to resolve (compilation error)
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
   pub fn as_num_bytes(self, target: Target) -> u8 {
      match self {
         IntWidth::Eight => 8,
         IntWidth::Four => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
         IntWidth::Pointer => target.pointer_width(),
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
   #[must_use]
   pub fn get_type_or_type_being_pointed_to(&self) -> &ExpressionType {
      match self {
         ExpressionType::Pointer(b) => b,
         _ => self,
      }
   }

   #[must_use]
   pub fn get_type_or_type_being_pointed_to_recursively(&self) -> &ExpressionType {
      match self {
         ExpressionType::Pointer(b) => b.get_type_or_type_being_pointed_to_recursively(),
         _ => self,
      }
   }

   #[must_use]
   pub fn is_concrete(&self) -> bool {
      match self {
         ExpressionType::Unknown(_) => false,
         ExpressionType::Pointer(v) | ExpressionType::Array(v, _) => v.is_concrete(),
         ExpressionType::ProcedureItem(_, type_args)
         | ExpressionType::Struct(_, type_args)
         | ExpressionType::Union(_, type_args) => type_args.iter().all(ExpressionType::is_concrete),
         ExpressionType::ProcedurePointer { parameters, ret_type } => parameters
            .iter()
            .chain(std::iter::once(ret_type.as_ref()))
            .all(ExpressionType::is_concrete),
         // other types can't contain unknown values, at least right now
         _ => true,
      }
   }

   #[must_use]
   pub fn is_concrete_shallow(&self) -> bool {
      match self {
         ExpressionType::Unknown(_) => false,
         ExpressionType::Pointer(v) | ExpressionType::Array(v, _) => !matches!(**v, ExpressionType::Unknown(_)),
         ExpressionType::ProcedureItem(_, type_args)
         | ExpressionType::Struct(_, type_args)
         | ExpressionType::Union(_, type_args) => type_args
            .iter()
            .all(|type_arg| !matches!(type_arg, ExpressionType::Unknown(_))),
         ExpressionType::ProcedurePointer { parameters, ret_type } => parameters
            .iter()
            .chain(std::iter::once(ret_type.as_ref()))
            .all(|p| !matches!(p, ExpressionType::Unknown(_))),
         // other types can't contain unknown values, at least right now
         _ => true,
      }
   }

   #[must_use]
   pub fn size_is_unknown(&self) -> bool {
      match self {
         ExpressionType::CompileError | ExpressionType::Unresolved { .. } => unreachable!(),
         ExpressionType::Unknown(_) | ExpressionType::GenericParam(_) => true,
         ExpressionType::Struct(_, type_arguments) | ExpressionType::Union(_, type_arguments) => {
            type_arguments.iter().any(ExpressionType::size_is_unknown)
         }
         ExpressionType::Int(_)
         | ExpressionType::Float(_)
         | ExpressionType::Bool
         | ExpressionType::Unit
         | ExpressionType::Never
         | ExpressionType::ProcedureItem(_, _)
         | ExpressionType::ProcedurePointer { .. }
         | ExpressionType::Enum(_)
         | ExpressionType::Pointer(_) => false,
         ExpressionType::Array(exp, _) => exp.size_is_unknown(),
      }
   }

   #[must_use]
   pub fn is_or_contains_or_points_to_error(&self) -> bool {
      match self {
         ExpressionType::CompileError => true,
         ExpressionType::Array(exp, _) | ExpressionType::Pointer(exp) => exp.is_or_contains_or_points_to_error(),
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
   pub fn is_aggregate(&self) -> bool {
      matches!(
         self,
         ExpressionType::Array(_, _) | ExpressionType::Struct(_, _) | ExpressionType::Union(_, _)
      )
   }

   #[must_use]
   pub fn as_roland_type_info<'i>(
      &self,
      interner: &'i Interner,
      udt: &UserDefinedTypeInfo,
      procedures: &SlotMap<ProcedureId, ProcedureNode>,
      type_variable_info: &TypeVariableManager,
   ) -> Cow<'i, str> {
      self.as_roland_type_info_inner(interner, udt, procedures, Some(type_variable_info))
   }

   #[must_use]
   fn as_roland_type_info_inner<'i>(
      &self,
      interner: &'i Interner,
      udt: &UserDefinedTypeInfo,
      procedures: &SlotMap<ProcedureId, ProcedureNode>,
      type_variable_info: Option<&TypeVariableManager>,
   ) -> Cow<'i, str> {
      match self {
         ExpressionType::Unknown(x) => {
            if let Some(tvi) = type_variable_info {
               let data = tvi.get_data(*x);
               if let Some(kt) = data.known_type.as_ref() {
                  kt.as_roland_type_info_inner(interner, udt, procedures, type_variable_info)
               } else {
                  match tvi.get_data(*x).constraint {
                     TypeConstraint::Int => Cow::Borrowed("?? Int"),
                     TypeConstraint::SignedInt => Cow::Borrowed("?? Signed Int"),
                     TypeConstraint::Float => Cow::Borrowed("?? Float"),
                     TypeConstraint::Enum => Cow::Borrowed("?? Enum"),
                     TypeConstraint::None => Cow::Borrowed("??"),
                  }
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
         ExpressionType::Unit => Cow::Borrowed("unit"),
         ExpressionType::Never => Cow::Borrowed("!"),
         ExpressionType::CompileError => Cow::Borrowed("ERROR"),
         ExpressionType::Struct(x, type_args) => {
            let name = interner.lookup(udt.struct_info.get(*x).unwrap().name);
            if name == "String" {
               Cow::Borrowed("String")
            } else if type_args.is_empty() {
               Cow::Owned(format!("Struct {}", name))
            } else {
               let g_args: String = type_args
                  .iter()
                  .map(|x| x.as_roland_type_info_inner(interner, udt, procedures, type_variable_info))
                  .collect::<Vec<_>>()
                  .join(", ");

               Cow::Owned(format!("Struct {}<{}>", name, g_args,))
            }
         }
         ExpressionType::Union(x, type_args) => {
            if type_args.is_empty() {
               Cow::Owned(format!(
                  "Union {}",
                  interner.lookup(udt.union_info.get(*x).unwrap().name)
               ))
            } else {
               let g_args: String = type_args
                  .iter()
                  .map(|x| x.as_roland_type_info_inner(interner, udt, procedures, type_variable_info))
                  .collect::<Vec<_>>()
                  .join(", ");

               Cow::Owned(format!(
                  "Union {}<{}>",
                  interner.lookup(udt.union_info.get(*x).unwrap().name),
                  g_args,
               ))
            }
         }
         ExpressionType::Enum(x) => {
            Cow::Owned(format!("Enum {}", interner.lookup(udt.enum_info.get(*x).unwrap().name)))
         }
         ExpressionType::Array(i_type, length) => Cow::Owned(format!(
            "[{}; {}]",
            i_type.as_roland_type_info_inner(interner, udt, procedures, type_variable_info),
            length
         )),
         ExpressionType::Pointer(i_type) => Cow::Owned(format!(
            "&{}",
            i_type.as_roland_type_info_inner(interner, udt, procedures, type_variable_info)
         )),
         ExpressionType::Unresolved { name: x, generic_args } => {
            if generic_args.is_empty() {
               Cow::Borrowed(interner.lookup(*x))
            } else {
               let g_args: String = generic_args
                  .iter()
                  .map(|x| x.as_roland_type_info_inner(interner, udt, procedures, type_variable_info))
                  .collect::<Vec<_>>()
                  .join(", ");

               Cow::Owned(format!("{}<{}>", interner.lookup(*x), g_args,))
            }
         }
         ExpressionType::GenericParam(x) => Cow::Borrowed(interner.lookup(*x)),
         ExpressionType::ProcedurePointer {
            parameters,
            ret_type: ret_val,
         } => {
            let params: String = parameters
               .iter()
               .map(|x| x.as_roland_type_info_inner(interner, udt, procedures, type_variable_info))
               .collect::<Vec<_>>()
               .join(", ");
            Cow::Owned(format!(
               "proc({}) -> {}",
               params,
               ret_val.as_roland_type_info_inner(interner, udt, procedures, type_variable_info)
            ))
         }
         ExpressionType::ProcedureItem(proc_id, type_arguments) => {
            let proc_name = procedures[*proc_id].definition.name.str;
            if type_arguments.is_empty() {
               Cow::Owned(format!("proc() {{{}}}", interner.lookup(proc_name),))
            } else {
               let type_argument_string = type_arguments
                  .iter()
                  .map(|x| x.as_roland_type_info_like_source(interner, udt))
                  .collect::<Vec<_>>()
                  .join("$");
               Cow::Owned(format!(
                  "proc() {{{}${}}}",
                  interner.lookup(proc_name),
                  type_argument_string
               ))
            }
         }
      }
   }

   #[must_use]
   pub fn as_roland_type_info_notv<'i>(
      &self,
      interner: &'i Interner,
      udt: &UserDefinedTypeInfo,
      procedures: &SlotMap<ProcedureId, ProcedureNode>,
   ) -> Cow<'i, str> {
      self.as_roland_type_info_inner(interner, udt, procedures, None)
   }

   #[must_use]
   pub fn as_roland_type_info_like_source<'i>(
      &self,
      interner: &'i Interner,
      udt: &UserDefinedTypeInfo,
   ) -> Cow<'i, str> {
      match self {
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
         ExpressionType::Unit => Cow::Borrowed("unit"),
         ExpressionType::Never => Cow::Borrowed("!"),
         ExpressionType::CompileError => Cow::Borrowed("ERROR"),
         ExpressionType::Struct(x, generic_args) => {
            if generic_args.is_empty() {
               Cow::Borrowed(interner.lookup(udt.struct_info.get(*x).unwrap().name))
            } else {
               let g_args: String = generic_args
                  .iter()
                  .map(|x| x.as_roland_type_info_like_source(interner, udt))
                  .collect::<Vec<_>>()
                  .join(", ");

               Cow::Owned(format!(
                  "{}<{}>",
                  interner.lookup(udt.struct_info.get(*x).unwrap().name),
                  g_args,
               ))
            }
         }
         ExpressionType::Union(x, generic_args) => {
            if generic_args.is_empty() {
               Cow::Borrowed(interner.lookup(udt.union_info.get(*x).unwrap().name))
            } else {
               let g_args: String = generic_args
                  .iter()
                  .map(|x| x.as_roland_type_info_like_source(interner, udt))
                  .collect::<Vec<_>>()
                  .join(", ");

               Cow::Owned(format!(
                  "{}<{}>",
                  interner.lookup(udt.union_info.get(*x).unwrap().name),
                  g_args,
               ))
            }
         }
         ExpressionType::Enum(x) => Cow::Borrowed(interner.lookup(udt.enum_info.get(*x).unwrap().name)),
         ExpressionType::Array(i_type, length) => Cow::Owned(format!(
            "[{}; {}]",
            i_type.as_roland_type_info_like_source(interner, udt),
            length
         )),
         ExpressionType::Pointer(i_type) => {
            Cow::Owned(format!("&{}", i_type.as_roland_type_info_like_source(interner, udt)))
         }
         ExpressionType::Unresolved { name: x, generic_args } => {
            if generic_args.is_empty() {
               Cow::Borrowed(interner.lookup(*x))
            } else {
               let g_args: String = generic_args
                  .iter()
                  .map(|x| x.as_roland_type_info_like_source(interner, udt))
                  .collect::<Vec<_>>()
                  .join(", ");

               Cow::Owned(format!("{}<{}>", interner.lookup(*x), g_args,))
            }
         }
         ExpressionType::GenericParam(x) => Cow::Borrowed(interner.lookup(*x)),
         ExpressionType::ProcedurePointer {
            parameters,
            ret_type: ret_val,
         } => {
            let params: String = parameters
               .iter()
               .map(|x| x.as_roland_type_info_like_source(interner, udt))
               .collect::<Vec<_>>()
               .join(", ");
            Cow::Owned(format!(
               "proc({}) -> {}",
               params,
               ret_val.as_roland_type_info_like_source(interner, udt)
            ))
         }
         ExpressionType::Unknown(_) | ExpressionType::ProcedureItem(_, _) => unreachable!(),
      }
   }
}
