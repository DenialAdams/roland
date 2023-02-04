use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::disjoint_set::DisjointSet;
use crate::interner::StrId;
use crate::parse::{ExpressionId, ExpressionPool, ExpressionTypeNode, VariableId};
use crate::size_info::SizeInfo;
use crate::source_info::SourceInfo;
use crate::type_data::{ExpressionType, ValueType};
use crate::Target;

pub mod type_and_procedure_info;
pub mod type_inference;
pub mod validator;

#[derive(Clone)]
pub struct ProcedureInfo {
   // This includes named parameters
   pub parameters: Vec<ExpressionType>,
   pub named_parameters: HashMap<StrId, ExpressionType>,
   pub type_parameters: Vec<IndexSet<StrId>>,
   pub ret_type: ExpressionType,
   pub location: SourceInfo,
   pub is_compiler_builtin: bool,
}

#[derive(Clone)]
pub struct EnumInfo {
   pub variants: IndexMap<StrId, SourceInfo>,
   pub location: SourceInfo,
   pub base_type: ValueType,
}

#[derive(Clone)]
pub struct StructInfo {
   pub field_types: IndexMap<StrId, ExpressionTypeNode>,
   pub default_values: IndexMap<StrId, ExpressionId>,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct GlobalInfo {
   pub expr_type: ExpressionType,
   pub location: SourceInfo,
   pub is_const: bool,
   pub name: StrId,
}

pub enum VariableKind {
   Parameter,
   Local,
   Global,
}

pub struct VariableDetails {
   pub var_type: ExpressionType,
   pub var_id: VariableId,
   pub declaration_location: SourceInfo,
   pub kind: VariableKind,
   pub depth: u64,
   pub used: bool,
}

pub struct ValidationContext<'a> {
   pub target: Target,
   pub procedure_info: &'a IndexMap<StrId, ProcedureInfo>,
   pub enum_info: &'a IndexMap<StrId, EnumInfo>,
   pub struct_info: &'a IndexMap<StrId, StructInfo>,
   pub global_info: &'a IndexMap<VariableId, GlobalInfo>,
   pub cur_procedure_info: Option<&'a ProcedureInfo>,
   pub string_literals: IndexSet<StrId>,
   pub variable_types: IndexMap<StrId, VariableDetails>,
   pub block_depth: u64,
   pub loop_depth: u64,
   pub unknown_ints: IndexSet<ExpressionId>,
   pub unknown_floats: IndexSet<ExpressionId>,
   pub expressions: &'a mut ExpressionPool,
   pub struct_size_info: HashMap<StrId, SizeInfo>,
   pub type_variables: DisjointSet,
   pub type_variable_definitions: HashMap<usize, ValueType>,
   pub cur_procedure_locals: IndexMap<VariableId, ExpressionType>,
   pub source_to_definition: IndexMap<SourceInfo, SourceInfo>,
   next_var_dont_access: VariableId,
}

impl ValidationContext<'_> {
   pub fn next_var(&mut self) -> VariableId {
      let ret_val = self.next_var_dont_access;
      self.next_var_dont_access = self.next_var_dont_access.next();
      ret_val
   }
}
