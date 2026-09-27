use crate::disjoint_set::DisjointSet;
use crate::semantic_analysis::type_inference::{occurs_check, try_merge_types};
use crate::type_data::{ExpressionType, IntType};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVariable(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeConstraint {
   Enum,
   Int,
   SignedInt,
   Float,
   None,
}

fn union_constraints(a: TypeConstraint, b: TypeConstraint) -> Result<TypeConstraint, ()> {
   match (a, b) {
      (TypeConstraint::None, _) => Ok(b),
      (_, TypeConstraint::None) => Ok(a),
      (TypeConstraint::Int, TypeConstraint::SignedInt) | (TypeConstraint::SignedInt, TypeConstraint::Int) => {
         Ok(TypeConstraint::SignedInt)
      }
      _ if a == b => Ok(a),
      _ => Err(()),
   }
}

pub fn constraint_compatible_with_concrete(constraint: TypeConstraint, concrete: &ExpressionType) -> bool {
   match constraint {
      TypeConstraint::None => true,
      TypeConstraint::Float => matches!(concrete, ExpressionType::Float(_)),
      TypeConstraint::SignedInt => matches!(concrete, ExpressionType::Int(IntType { signed: true, .. })),
      TypeConstraint::Int => matches!(concrete, ExpressionType::Int(_)),
      TypeConstraint::Enum => matches!(concrete, ExpressionType::Enum(_)),
   }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVariableData {
   pub constraint: TypeConstraint,
   pub known_type: Option<ExpressionType>,
}

impl TypeVariableData {
   pub fn add_constraint(&mut self, constraint: TypeConstraint) -> Result<(), ()> {
      self.constraint = union_constraints(self.constraint, constraint)?;
      Ok(())
   }
}

pub struct TypeVariableManager {
   type_variable_data: Vec<TypeVariableData>,
   disjoint_set: DisjointSet,
}

impl TypeVariableManager {
   pub fn new() -> TypeVariableManager {
      TypeVariableManager {
         disjoint_set: DisjointSet::new(),
         type_variable_data: Vec::new(),
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

   pub fn union(&mut self, x: TypeVariable, y: TypeVariable) -> Result<(), ()> {
      let (x_rep, x_data) = self.get_rep_and_data(x);
      let (y_rep, y_data) = self.get_rep_and_data(y);

      if x_rep == y_rep {
         return Ok(());
      }

      let new_constraint = union_constraints(x_data.constraint, y_data.constraint)?;

      if let Some(kt) = x_data.known_type.as_ref()
         && occurs_check(y_rep, kt, self)
      {
         return Err(());
      }

      if let Some(kt) = y_data.known_type.as_ref()
         && occurs_check(x_rep, kt, self)
      {
         return Err(());
      }

      let known_type = match (x_data.known_type.clone(), y_data.known_type.clone()) {
         (None, None) => None,
         (None, r @ Some(_)) => r,
         (l @ Some(_), None) => l,
         (Some(l), Some(r)) => {
            if !try_merge_types(&l, &r, self) {
               return Err(());
            }

            Some(l)
         }
      };

      if let Some(known_type) = known_type.as_ref()
         && !constraint_compatible_with_concrete(new_constraint, known_type)
      {
         return Err(());
      }

      self.disjoint_set.union_representatives(x_rep.0, y_rep.0);
      let new_data = self.get_data_mut(x);
      new_data.constraint = new_constraint;
      new_data.known_type = known_type;
      Ok(())
   }

   pub fn get_data(&self, x: TypeVariable) -> &TypeVariableData {
      let rep = self.find(x);
      &self.type_variable_data[rep.0]
   }

   pub fn get_data_mut(&mut self, x: TypeVariable) -> &mut TypeVariableData {
      let rep = self.find(x);
      &mut self.type_variable_data[rep.0]
   }

   pub fn get_rep_and_data(&self, x: TypeVariable) -> (TypeVariable, &TypeVariableData) {
      let rep = self.find(x);
      (rep, &self.type_variable_data[rep.0])
   }
}
