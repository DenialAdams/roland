use std::collections::HashMap;

use indexmap::IndexMap;

use crate::interner::{Interner, StrId};
use crate::parse::{Expression, ExpressionId, ExpressionPool, Program, VariableId};
use crate::semantic_analysis::StructInfo;
use crate::type_data::ExpressionType;
use crate::typed_index_vec::Handle;

pub fn lower_single_expression(
   expressions: &mut ExpressionPool,
   expression_id: ExpressionId,
   const_replacements: &HashMap<VariableId, ExpressionId>,
   struct_info: &IndexMap<StrId, StructInfo>,
   interner: &Interner,
) {
   match &expressions[expression_id].expression {
      Expression::Variable(x) => {
         if let Some(replacement_index) = const_replacements.get(x).copied() {
            expressions[expression_id].expression = expressions[replacement_index].expression.clone();
         }
      }
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::FieldAccess(fields, other_exp) => {
         // Do this check first to try and skip most struct field accesses
         if fields.last().map(|x| interner.lookup(*x) != "length").unwrap() {
            return;
         }

         if let Expression::StringLiteral(id) = expressions[*other_exp].expression {
            let strlen = interner.lookup(id).len();
            expressions[expression_id].expression = Expression::IntLiteral {
               val: strlen as u64,
               synthetic: true,
            };
            return;
         }

         let mut lhs_type = expressions[*other_exp].exp_type.as_ref().unwrap();
         let mut remaining_fields = fields.as_slice();

         while !remaining_fields.is_empty() {
            let field = remaining_fields[0];
            match lhs_type {
               ExpressionType::Struct(struct_name) => {
                  let struct_fields = &struct_info.get(struct_name).unwrap().field_types;
                  lhs_type = &struct_fields.get(&field).unwrap().e_type;
               }
               ExpressionType::Array(_, _) => {
                  break;
               }
               _ => unreachable!(),
            }
            remaining_fields = if remaining_fields.is_empty() {
               &[]
            } else {
               &remaining_fields[1..]
            };
         }

         let length_of_array = match lhs_type {
            ExpressionType::Array(_, len) => *len,
            _ => return,
         };

         expressions[expression_id].expression = Expression::IntLiteral {
            val: u64::from(length_of_array),
            synthetic: true,
         };
      }
      _ => (),
   }
}

pub fn lower_consts(program: &mut Program, expressions: &mut ExpressionPool, interner: &mut Interner) {
   let mut const_replacements: HashMap<VariableId, ExpressionId> = HashMap::new();

   for p_const in program.consts.drain(..) {
      const_replacements.insert(p_const.var_id, p_const.value);
   }
   for i in 0..expressions.len() {
      lower_single_expression(
         expressions,
         ExpressionId::new(i),
         &const_replacements,
         &program.struct_info,
         interner,
      );
   }
}
