use crate::Program;
use crate::interner::Interner;
use crate::parse::{Expression, all_expression_pools_mut};

pub fn lower_named_args(p: &mut Program, interner: &Interner) {
   for proc in p.procedures.values_mut() {
      let first_named_param_index = proc.definition.parameters.iter().position(|x| x.named);
      if let Some(i) = first_named_param_index {
         // It doesn't really matter how we sort these, as long as we do it consistently for arguments
         // AND that there are no equal elements (in this case, we already checked that parameters don't have the same name)
         proc.definition.parameters[i..].sort_unstable_by_key(|x| interner.lookup(x.name));
      }
   }

   for ast in all_expression_pools_mut(&mut p.global_exprs, &mut p.procedure_bodies) {
      for v in ast.values_mut() {
         let Expression::ProcedureCall { proc_expr: _, args } = &mut v.expression else {
            continue;
         };
         let first_named_arg = args.iter().position(|x| x.name.is_some());
         let Some(position) = first_named_arg else {
            continue;
         };
         args[position..].sort_unstable_by_key(|x| interner.lookup(x.name.unwrap()));
         for named_arg in args[position..].iter_mut() {
            named_arg.name = None;
         }
      }
   }
}
