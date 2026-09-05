use std::collections::HashMap;

use crate::interner::StrId;
use crate::parse::VariableId;
use crate::semantic_analysis::VariableScopeKind;
use crate::source_info::SourceInfo;

type AllVarsIdx = usize;

struct VarEntry {
   details: VariableDetails,
   shadowing: Option<AllVarsIdx>,
   name: StrId,
}

pub struct SymbolTable {
   all_vars: Vec<VarEntry>,
   name_table: HashMap<StrId, AllVarsIdx>,
}

pub struct ScopeMarker(usize);

impl SymbolTable {
   pub fn new() -> SymbolTable {
      SymbolTable {
         all_vars: Vec::new(),
         name_table: HashMap::new(),
      }
   }

   pub fn declare(&mut self, name: StrId, details: VariableDetails) {
      let shadowing = self.name_table.insert(name, self.all_vars.len());
      self.all_vars.push(VarEntry {
         details,
         shadowing,
         name,
      });
   }

   pub fn is_name_in_scope(&self, name: StrId) -> bool {
      self.name_table.contains_key(&name)
   }

   pub fn get_mut(&mut self, name: StrId) -> Option<&mut VariableDetails> {
      let idx = *self.name_table.get(&name)?;
      Some(&mut self.all_vars[idx].details)
   }

   pub fn start_scope(&self) -> ScopeMarker {
      ScopeMarker(self.all_vars.len())
   }

   #[allow(clippy::needless_pass_by_value)] // ScopeMarker is supposed to be moved to discourage double falling
   pub fn fall_out_of_scope(&mut self, scope_marker: ScopeMarker, mut callback: impl FnMut(&VariableDetails, StrId)) {
      let first_var_in_scope = scope_marker.0;
      for mut entry in self.all_vars.drain(first_var_in_scope..).rev() {
         match entry.shadowing {
            Some(hidden) => {
               self.name_table.insert(entry.name, hidden);
            }
            None => {
               self.name_table.remove(&entry.name);
            }
         }
         callback(&mut entry.details, entry.name);
      }
   }
}

pub struct VariableDetails {
   pub var_id: VariableId,
   pub declaration_location: SourceInfo,
   pub kind: VariableScopeKind,
   pub used: bool,
}
