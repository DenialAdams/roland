use std::collections::{HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};

use crate::disjoint_set::DisjointSet;
use crate::interner::StrId;
use crate::parse::{ExpressionId, ExpressionPool};
use crate::size_info::SizeInfo;
use crate::source_info::SourceInfo;
use crate::type_data::ExpressionType;
use crate::Target;

pub mod type_and_procedure_info;
pub mod type_inference;
pub mod validator;

#[derive(Clone)]
pub struct ProcedureInfo {
   // This includes named parameters
   pub parameters: Vec<ExpressionType>,
   pub named_parameters: HashMap<StrId, ExpressionType>,
   pub type_parameters: usize,
   pub ret_type: ExpressionType,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct EnumInfo {
   pub variants: IndexSet<StrId>,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct StructInfo {
   pub field_types: IndexMap<StrId, ExpressionType>,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct StaticInfo {
   pub static_type: ExpressionType,
   pub location: SourceInfo,
   pub is_const: bool,
}

pub enum ScopedVariableKind {
   Parameter,
   Local,
}

pub struct ScopedVariableDetails {
   pub var_type: ExpressionType,
   pub declaration_location: SourceInfo,
   pub kind: ScopedVariableKind,
   pub depth: u64,
   pub used: bool,
}

pub struct ValidationContext<'a> {
   pub target: Target,
   pub procedure_info: &'a IndexMap<StrId, ProcedureInfo>,
   pub enum_info: &'a IndexMap<StrId, EnumInfo>,
   pub struct_info: &'a IndexMap<StrId, StructInfo>,
   pub static_info: &'a IndexMap<StrId, StaticInfo>,
   pub cur_procedure_info: Option<&'a ProcedureInfo>,
   pub string_literals: IndexSet<StrId>,
   pub variable_types: IndexMap<StrId, ScopedVariableDetails>,
   pub error_count: u64,
   pub block_depth: u64,
   pub loop_depth: u64,
   pub unknown_ints: IndexSet<ExpressionId>,
   pub unknown_floats: IndexSet<ExpressionId>,
   pub expressions: &'a mut ExpressionPool,
   pub struct_size_info: HashMap<StrId, SizeInfo>,
   pub type_variables: DisjointSet,
   pub type_variable_definitions: HashMap<usize, ExpressionType>,
   pub cur_procedure_locals: IndexMap<StrId, HashSet<ExpressionType>>,
}
