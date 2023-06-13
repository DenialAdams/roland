use std::collections::HashMap;

use crate::disjoint_set::DisjointSet;
use crate::type_data::ExpressionType;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVariable(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeConstraint {
   Int,
   SignedInt,
   Float,
   None,
}

fn union_constraints(a: TypeConstraint, b: TypeConstraint) -> TypeConstraint {
   match (a, b) {
      (TypeConstraint::None, _) => b,
      (_, TypeConstraint::None) => a,
      (TypeConstraint::Int, TypeConstraint::SignedInt) => TypeConstraint::SignedInt,
      (TypeConstraint::SignedInt, TypeConstraint::Int) => TypeConstraint::SignedInt,
      _ => {
         debug_assert!(a == b);
         a
      }
   }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVariableData {
   pub constraint: TypeConstraint,
   pub known_type: Option<ExpressionType>,
}

impl TypeVariableData {
   pub fn add_constraint(&mut self, constraint: TypeConstraint) -> Result<(), ()> {
      match (self.constraint, constraint) {
         (x, y) if x == y => Ok(()),
         (TypeConstraint::None, any_constraint) => {
            self.constraint = any_constraint;
            Ok(())
         }
         (TypeConstraint::Int, refined_constraint @ TypeConstraint::SignedInt) => {
            self.constraint = refined_constraint;
            Ok(())
         }
         _ => Err(()),
      }
   }
}

pub struct TypeVariableManager {
   type_variable_data: HashMap<usize, TypeVariableData>,
   disjoint_set: DisjointSet,
}

impl TypeVariableManager {
   pub fn new() -> TypeVariableManager {
      TypeVariableManager {
         disjoint_set: DisjointSet::new(),
         type_variable_data: HashMap::new(),
      }
   }

   pub fn new_type_variable(&mut self, constraint: TypeConstraint) -> TypeVariable {
      let new_tv = self.disjoint_set.add_new_set();
      self.type_variable_data.insert(
         new_tv,
         TypeVariableData {
            constraint,
            known_type: None,
         },
      );
      TypeVariable(new_tv)
   }

   pub fn find(&self, x: TypeVariable) -> TypeVariable {
      TypeVariable(self.disjoint_set.find(x.0))
   }

   pub fn union(&mut self, x: TypeVariable, y: TypeVariable) {
      let new_constraint = union_constraints(self.get_data(x).constraint, self.get_data(y).constraint);
      let known_type = {
         match (self.get_data_mut(x).known_type.take(), self.get_data_mut(y).known_type.take()) {
            (None, None) => None,
            (None, r @ Some(_)) => r,
            (l @ Some(_), None) => l,
            (l @ Some(_), r @ Some(_)) => {
               debug_assert!(l == r);
               l
            },
        }
      };
      self.disjoint_set.union(x.0, y.0);
      let new_data = self.get_data_mut(x);
      new_data.constraint = new_constraint;
      new_data.known_type = known_type;
   }

   pub fn get_data(&self, x: TypeVariable) -> &TypeVariableData {
      let rep = self.find(x);
      self.type_variable_data.get(&rep.0).unwrap()
   }

   pub fn get_data_mut(&mut self, x: TypeVariable) -> &mut TypeVariableData {
      let rep = self.find(x);
      self.type_variable_data.get_mut(&rep.0).unwrap()
   }
}
