use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use self::type_variables::TypeVariableManager;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, ExpressionId, ExpressionTypeNode, ExternalProcImplSource, ProcedureId, VariableId,
};
use crate::size_info::SizeInfo;
use crate::source_info::SourceInfo;
use crate::type_data::ExpressionType;
use crate::Target;

pub mod type_and_procedure_info;
pub mod type_inference;
pub mod type_variables;
pub mod validator;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum ProcImplSource {
   Builtin,
   External,
   ProcedureId(ProcedureId),
}

impl From<ExternalProcImplSource> for ProcImplSource {
   fn from(value: ExternalProcImplSource) -> Self {
      match value {
         ExternalProcImplSource::Builtin => ProcImplSource::Builtin,
         ExternalProcImplSource::External => ProcImplSource::External,
      }
   }
}

#[derive(Clone)]
pub struct ProcedureInfo {
   // This includes named parameters
   pub parameters: Vec<ExpressionType>,
   pub named_parameters: HashMap<StrId, ExpressionType>,
   pub type_parameters: IndexMap<StrId, IndexSet<StrId>>,
   pub ret_type: ExpressionType,
   pub location: SourceInfo,
   pub proc_impl_source: ProcImplSource,
}

#[derive(Clone)]
pub struct EnumInfo {
   pub variants: IndexMap<StrId, SourceInfo>,
   pub location: SourceInfo,
   pub base_type: ExpressionType,
}

#[derive(Clone)]
pub struct StructInfo {
   pub field_types: IndexMap<StrId, ExpressionTypeNode>,
   pub default_values: IndexMap<StrId, ExpressionId>,
   pub location: SourceInfo,
}

#[derive(Clone, Debug, PartialEq)]
pub enum GlobalKind {
   Static,
   Const,
}

#[derive(Clone, Debug)]
pub struct GlobalInfo {
   pub expr_type: ExpressionTypeNode,
   pub initializer: Option<ExpressionId>,
   pub location: SourceInfo,
   pub kind: GlobalKind,
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
   pub used: bool,
}

pub struct ValidationContext<'a> {
   pub target: Target,
   pub procedure_info: &'a IndexMap<StrId, ProcedureInfo>,
   pub enum_info: &'a IndexMap<StrId, EnumInfo>,
   pub struct_info: &'a IndexMap<StrId, StructInfo>,
   pub global_info: &'a IndexMap<VariableId, GlobalInfo>,
   pub cur_procedure_info: Option<&'a ProcedureInfo>,
   pub variable_types: IndexMap<StrId, VariableDetails>,
   pub loop_depth: u64,
   pub unknown_literals: IndexSet<ExpressionId>,
   pub ast: &'a mut AstPool,
   pub struct_size_info: HashMap<StrId, SizeInfo>,
   pub type_variables: TypeVariableManager,
   pub cur_procedure_locals: IndexMap<VariableId, ExpressionType>,
   pub source_to_definition: IndexMap<SourceInfo, SourceInfo>,
   pub interner: &'a mut Interner,
   next_var_dont_access: VariableId,
}

impl ValidationContext<'_> {
   pub fn next_var(&mut self) -> VariableId {
      let ret_val = self.next_var_dont_access;
      self.next_var_dont_access = self.next_var_dont_access.next();
      ret_val
   }
}
