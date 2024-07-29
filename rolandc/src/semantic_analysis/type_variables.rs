use crate::disjoint_set::DisjointSet;
use crate::type_data::ExpressionType;

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
   pub type_variable_data: Vec<TypeVariableData>,
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
      let new_constraint = union_constraints(self.get_data(x).constraint, self.get_data(y).constraint)?;
      let known_type = match (
         self.get_data_mut(x).known_type.take(),
         self.get_data_mut(y).known_type.take(),
      ) {
         (None, None) => None,
         (None, r @ Some(_)) => r,
         (l @ Some(_), None) => l,
         (l @ Some(_), r @ Some(_)) if l == r => l,
         _ => return Err(()),
      };
      self.disjoint_set.union(x.0, y.0);
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
}
