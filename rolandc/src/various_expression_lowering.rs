use crate::interner::{Interner, StrId};
use crate::parse::{Expression, ExpressionId, ExpressionPool, Program};
use crate::size_info::SizeInfo;
use crate::type_data::{ValueType, ExpressionType};
use crate::typed_index_vec::Handle;
use std::collections::HashMap;

pub fn lower_consts(
   struct_size_info: &HashMap<StrId, SizeInfo>,
   program: &mut Program,
   expressions: &mut ExpressionPool,
   interner: &mut Interner,
) {
   let mut const_replacements: HashMap<StrId, ExpressionId> = HashMap::new();

   for p_const in program.consts.drain(0..) {
      const_replacements.insert(p_const.name.identifier, p_const.value);
   }

   let sizeof_proc_id = interner.intern("sizeof");
   for i in 0..expressions.len() {
      match &expressions[ExpressionId::new(i)].expression {
         Expression::Variable(x) => {
            if let Some(replacement_index) = const_replacements.get(x).copied() {
               expressions[ExpressionId::new(i)].expression = expressions[replacement_index].expression.clone();
            }
         }
         Expression::ProcedureCall {
            proc_name: x,
            generic_args,
            args: _args,
         } => {
            if *x != sizeof_proc_id {
               continue;
            }

            let type_size =
               crate::size_info::sizeof_type_mem(&generic_args[0].gtype, &program.enum_info, struct_size_info);

            expressions[ExpressionId::new(i)].expression = Expression::IntLiteral(i128::from(type_size));
         }
         Expression::FieldAccess(_, other_exp) => {
            let length_of_array = match expressions[*other_exp].exp_type.as_ref().unwrap() {
               ExpressionType::Value(ValueType::Array(_, len)) => *len,
               _ => continue,
            };

            expressions[ExpressionId::new(i)].expression = Expression::IntLiteral(length_of_array);
         }
         _ => (),
      }
   }
}
