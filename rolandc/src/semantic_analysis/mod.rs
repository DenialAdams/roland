use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};
use slotmap::SlotMap;

use self::type_variables::TypeVariableManager;
use crate::Target;
use crate::interner::{Interner, StrId};
use crate::monomorphization::SpecializationRequest;
use crate::parse::{
   AstPool, ExpressionId, ExpressionTypeNode, ProcedureId, ProcedureNode, StructId, UserDefinedTypeId,
   UserDefinedTypeInfo, VariableId,
};
use crate::size_info::{StructSizeInfo, UnionSizeInfo};
use crate::source_info::SourceInfo;
use crate::type_data::ExpressionType;

pub mod definite_assignment;
pub mod type_and_procedure_info;
pub mod type_inference;
pub mod type_variables;
pub mod validator;

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

#[derive(Clone)]
pub struct AliasInfo {
   pub target_type: ExpressionTypeNode,
   pub location: SourceInfo,
   pub name: StrId,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum StorageKind {
   Static,
   Const,
}

#[derive(Clone, Debug)]
pub struct GlobalInfo {
   pub expr_type: ExpressionTypeNode,
   pub initializer: Option<ExpressionId>,
   pub location: SourceInfo,
   pub kind: StorageKind,
   pub name: StrId,
}

pub enum VariableScopeKind {
   Parameter,
   Local,
   Global,
}

pub struct VariableDetails {
   pub var_id: VariableId,
   pub declaration_location: SourceInfo,
   pub kind: VariableScopeKind,
   pub used: bool,
}

pub struct OwnedValidationContext {
   pub target: Target,
   pub cur_procedure: Option<ProcedureId>,
   pub variable_types: IndexMap<StrId, VariableDetails>,
   pub loop_depth: u64,
   pub type_variables: TypeVariableManager,
   pub cur_procedure_locals: IndexMap<VariableId, ExpressionType>,
   pub string_struct_id: StructId,
   pub procedures_to_specialize: Vec<SpecializationRequest>,
}

pub struct ValidationContext<'a, 'b> {
   pub owned: &'b mut OwnedValidationContext,
   pub ast: &'a mut AstPool,
   pub source_to_definition: &'a mut IndexMap<SourceInfo, SourceInfo>,
   pub interner: &'a mut Interner,
   pub procedures: &'a SlotMap<ProcedureId, ProcedureNode>,
   pub user_defined_type_name_table: &'a HashMap<StrId, UserDefinedTypeId>,
   pub proc_name_table: &'a HashMap<StrId, ProcedureId>,
   pub user_defined_types: &'a UserDefinedTypeInfo,
   pub global_info: &'a mut IndexMap<VariableId, GlobalInfo>,
   pub templated_types: &'a HashMap<UserDefinedTypeId, IndexSet<StrId>>,
   next_var_dont_access: &'a mut VariableId,
}

impl ValidationContext<'_, '_> {
   pub fn next_var(&mut self) -> VariableId {
      let ret_val = *self.next_var_dont_access;
      *self.next_var_dont_access = self.next_var_dont_access.next();
      ret_val
   }
}
