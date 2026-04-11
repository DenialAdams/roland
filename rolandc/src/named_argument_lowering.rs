use crate::Program;
use crate::parse::{Expression, all_expression_pools_mut};

pub fn lower_named_args(p: &mut Program) {
   for ast in all_expression_pools_mut(&mut p.global_exprs, &mut p.procedure_bodies) {
      for v in ast.values_mut() {
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
   }
   // We only lower arguments - parameters are lowered very early on, even before type checking
   // (There's probably no good reason for that, and maybe we colocate them eventually)
}
