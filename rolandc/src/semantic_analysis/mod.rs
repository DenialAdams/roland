use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};
use slotmap::SecondaryMap;

use self::type_variables::TypeVariableManager;
use crate::interner::{Interner, StrId};
use crate::parse::{
   AstPool, ExpressionId, ExpressionTypeNode, ProcedureId, StrNode, UserDefinedTypeId, UserDefinedTypeInfo, VariableId,
};
use crate::size_info::{StructSizeInfo, UnionSizeInfo};
use crate::source_info::SourceInfo;
use crate::type_data::ExpressionType;
use crate::Target;

pub mod type_and_procedure_info;
pub mod type_inference;
pub mod type_variables;
pub mod validator;

#[derive(Clone)]
pub struct ProcedureInfo {
   // This includes named parameters
   pub parameters: Vec<ExpressionType>,
   pub named_parameters: HashMap<StrId, ExpressionType>,
   pub type_parameters: IndexMap<StrId, IndexSet<StrId>>,
   pub ret_type: ExpressionType,
   pub location: SourceInfo,
   pub name: StrNode,
   pub is_builtin: bool,
}

#[derive(Clone)]
pub struct EnumInfo {
   pub variants: IndexMap<StrId, SourceInfo>,
   pub location: SourceInfo,
   pub base_type: ExpressionType,
   pub name: StrId,
}

#[derive(Clone)]
pub struct StructInfo {
   pub field_types: IndexMap<StrId, ExpressionTypeNode>,
   pub default_values: IndexMap<StrId, ExpressionId>,
   pub location: SourceInfo,
   pub size: Option<StructSizeInfo>,
   pub name: StrId,
}

#[derive(Clone)]
pub struct UnionInfo {
   pub field_types: IndexMap<StrId, ExpressionTypeNode>,
   pub location: SourceInfo,
   pub size: Option<UnionSizeInfo>,
   pub name: StrId,
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
   pub procedure_info: &'a SecondaryMap<ProcedureId, ProcedureInfo>,
   pub user_defined_type_name_table: &'a HashMap<StrId, UserDefinedTypeId>,
   pub proc_name_table: &'a HashMap<StrId, ProcedureId>,
   pub user_defined_types: &'a UserDefinedTypeInfo,
   pub global_info: &'a IndexMap<VariableId, GlobalInfo>,
   pub cur_procedure_info: Option<&'a ProcedureInfo>,
   pub variable_types: IndexMap<StrId, VariableDetails>,
   pub loop_depth: u64,
   pub unknown_literals: IndexSet<ExpressionId>,
   pub ast: &'a mut AstPool,
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
