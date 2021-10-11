use std::collections::{HashMap, HashSet};

use indexmap::IndexMap;

use crate::lex::SourceInfo;
use crate::type_data::ExpressionType;

pub mod type_inference;
pub mod validator;

pub struct ProcedureInfo {
   pub pure: bool,
   pub parameters: Vec<ExpressionType>,
   pub ret_type: ExpressionType,
   pub procedure_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct StructInfo {
   pub field_types: IndexMap<String, ExpressionType>,
   pub struct_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct StaticInfo {
   pub static_type: ExpressionType,
   pub static_begin_location: SourceInfo,
}

pub struct ValidationContext<'a> {
   pub procedure_info: &'a IndexMap<String, ProcedureInfo>,
   pub struct_info: &'a IndexMap<String, StructInfo>,
   pub static_info: &'a IndexMap<String, StaticInfo>,
   pub cur_procedure_info: Option<&'a ProcedureInfo>,
   pub string_literals: HashSet<String>,
   pub variable_types: HashMap<String, (ExpressionType, u64)>,
   pub error_count: u64,
   pub block_depth: u64,
   pub loop_depth: u64,
   pub unknown_ints: u64,
   pub unknown_floats: u64,
}
