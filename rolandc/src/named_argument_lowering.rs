use crate::parse::Expression;
use crate::Program;

pub fn lower_named_args(p: &mut Program) {
   for v in p.ast.expressions.values_mut() {
      let Expression::ProcedureCall { proc_expr: _, args } = &mut v.expression else {
         continue;
      };
      let first_named_arg = args.iter().position(|x| x.name.is_some());
      let Some(position) = first_named_arg else {
         continue;
      };
      args[position..].sort_unstable_by_key(|x| x.name.unwrap());
      for named_arg in args[position..].iter_mut() {
         named_arg.name = None;
      }
   }
   // We only lower arguments - parameters are lowered very early on, even before type checking
   // (There's probably no good reason for that, and maybe we colocate them eventually)
}
