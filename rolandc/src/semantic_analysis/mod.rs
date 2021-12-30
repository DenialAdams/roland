use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::interner::StrId;
use crate::lex::SourceInfo;
use crate::parse::{ExpressionIndex, ExpressionPool};
use crate::type_data::ExpressionType;
use crate::Target;

pub mod type_inference;
pub mod validator;

pub struct ProcedureInfo {
   // This includes named parameters
   pub parameters: Vec<ExpressionType>,
   pub named_parameters: HashMap<StrId, ExpressionType>,
   pub type_parameters: usize,
   pub ret_type: ExpressionType,
   pub procedure_begin_location: SourceInfo,
   pub is_external: bool,
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

#[derive(Clone, Debug)]
pub struct StaticInfo {
   pub static_type: ExpressionType,
   pub begin_location: SourceInfo,
   pub is_const: bool,
}

pub struct ValidationContext<'a> {
   pub target: Target,
   pub procedure_info: &'a IndexMap<StrId, ProcedureInfo>,
   pub enum_info: &'a IndexMap<StrId, EnumInfo>,
   pub struct_info: &'a IndexMap<StrId, StructInfo>,
   pub static_info: &'a IndexMap<StrId, StaticInfo>,
   pub cur_procedure_info: Option<&'a ProcedureInfo>,
   pub string_literals: IndexSet<StrId>,
   pub variable_types: HashMap<StrId, (ExpressionType, u64)>,
   pub virtual_vars: IndexSet<ExpressionIndex>,
   pub error_count: u64,
   pub block_depth: u64,
   pub loop_depth: u64,
   pub unknown_ints: u64,
   pub unknown_floats: u64,
   pub expressions: &'a mut ExpressionPool,
}
