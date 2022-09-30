use std::collections::HashMap;

use indexmap::IndexMap;

use crate::interner::{Interner, StrId};
use crate::parse::{Expression, ExpressionId, ExpressionPool, Program, VariableId};
use crate::semantic_analysis::{EnumInfo, StructInfo};
use crate::size_info::SizeInfo;
use crate::type_data::{ExpressionType, ValueType};
use crate::typed_index_vec::Handle;

pub fn lower_single_expression(
   expressions: &mut ExpressionPool,
   expression_id: ExpressionId,
   const_replacements: &HashMap<VariableId, ExpressionId>,
   sizeof_proc_id: StrId,
   alignof_proc_id: StrId,
   length_id: StrId,
   struct_info: &IndexMap<StrId, StructInfo>,
   struct_size_info: &HashMap<StrId, SizeInfo>,
   enum_info: &IndexMap<StrId, EnumInfo>,
   interner: &Interner,
) {
   match &expressions[expression_id].expression {
      Expression::Variable(x) => {
         if let Some(replacement_index) = const_replacements.get(x).copied() {
            expressions[expression_id].expression = expressions[replacement_index].expression.clone();
         }
      }
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::ProcedureCall {
         proc_name: x,
         generic_args,
         args: _args,
      } => {
         if x.identifier == sizeof_proc_id {
            let type_size = crate::size_info::sizeof_type_mem(&generic_args[0].gtype, enum_info, struct_size_info);

            expressions[expression_id].expression = Expression::IntLiteral {
               val: u64::from(type_size),
               synthetic: true,
            };
         } else if x.identifier == alignof_proc_id {
            let type_size = crate::size_info::mem_alignment(&generic_args[0].gtype, enum_info, struct_size_info);

            expressions[expression_id].expression = Expression::IntLiteral {
               val: u64::from(type_size),
               synthetic: true,
            };
         }
      }
      Expression::FieldAccess(fields, other_exp) => {
         // Do this check first to try and skip most struct field accesses
         if fields.last().map(|x| *x != length_id).unwrap() {
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
               ExpressionType::Value(ValueType::Struct(struct_name)) => {
                  let struct_fields = &struct_info.get(struct_name).unwrap().field_types;
                  lhs_type = struct_fields.get(&field).unwrap();
               }
               ExpressionType::Value(ValueType::Array(_, _)) => {
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
            ExpressionType::Value(ValueType::Array(_, len)) => *len,
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

   for p_const in program.consts.drain(0..) {
      const_replacements.insert(p_const.var_id, p_const.value);
   }

   let sizeof_proc_id = interner.intern("sizeof");
   let alignof_proc_id = interner.intern("alignof");
   let length_id = interner.intern("length");
   for i in 0..expressions.len() {
      lower_single_expression(
         expressions,
         ExpressionId::new(i),
         &const_replacements,
         sizeof_proc_id,
         alignof_proc_id,
         length_id,
         &program.struct_info,
         &program.struct_size_info,
         &program.enum_info,
         interner,
      );
   }
}
