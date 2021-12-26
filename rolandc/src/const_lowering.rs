use crate::interner::{StrId, Interner};
use crate::parse::{Expression, ExpressionIndex, ExpressionPool, Program};
use crate::typed_index_vec::Handle;
use std::collections::HashMap;

pub fn lower_consts(program: &mut Program, expressions: &mut ExpressionPool, interner: &mut Interner) {
   let mut const_replacements: HashMap<StrId, ExpressionIndex> = HashMap::new();

   for p_const in program.consts.drain(0..) {
      const_replacements.insert(p_const.name.identifier, p_const.value);
   }

   let sizeof_proc_id = interner.intern("sizeof");
   for i in 0..expressions.len() {
      match &expressions[ExpressionIndex::new(i)].expression {
         Expression::Variable(x) => {
            if let Some(replacement_index) = const_replacements.get(x).copied() {
               expressions[ExpressionIndex::new(i)].expression = expressions[replacement_index].expression.clone();
            }
         },
         Expression::ProcedureCall{ proc_name: x, generic_args, args: _args} => {
            if *x != sizeof_proc_id {
               continue;
            }

            //let type_size = crate::wasm::sizeof_type_mem(&generic_args[0].gtype, &program.enum_info, todo!());

            //expressions[ExpressionIndex::new(i)].expression = Expression::IntLiteral(i128::from(type_size));
         }
         _ => (),
      }
   }
}
