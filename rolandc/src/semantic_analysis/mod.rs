use std::collections::{HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};

use crate::interner::StrId;
use crate::lex::SourceInfo;
use crate::type_data::ExpressionType;

pub mod type_inference;
pub mod validator;

pub struct ProcedureInfo {
   pub pure: bool,
   // This includes named parameters
   pub parameters: Vec<ExpressionType>,
   pub named_parameters: HashMap<StrId, ExpressionType>,
   pub ret_type: ExpressionType,
   pub procedure_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct EnumInfo {
   pub variants: IndexSet<StrId>,
   pub enum_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct StructInfo {
   pub field_types: IndexMap<StrId, ExpressionType>,
   pub struct_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct StaticInfo {
   pub static_type: ExpressionType,
   pub static_begin_location: SourceInfo,
}

pub struct ValidationContext<'a> {
   pub procedure_info: &'a IndexMap<StrId, ProcedureInfo>,
   pub enum_info: &'a IndexMap<StrId, EnumInfo>,
   pub struct_info: &'a IndexMap<StrId, StructInfo>,
   pub static_info: &'a IndexMap<StrId, StaticInfo>,
   pub cur_procedure_info: Option<&'a ProcedureInfo>,
   pub string_literals: HashSet<StrId>,
   pub variable_types: HashMap<StrId, (ExpressionType, u64)>,
   pub error_count: u64,
   pub block_depth: u64,
   pub loop_depth: u64,
   pub unknown_ints: u64,
   pub unknown_floats: u64,
}
