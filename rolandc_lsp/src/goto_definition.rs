use std::path::Path;

use rolandc::interner::Interner;
use rolandc::parse::Expression;
use rolandc::source_info::{SourceInfo, SourcePosition};
use rolandc::CompilationContext;

use crate::roland_source_path_to_canon_path;

#[must_use]
fn span_contains(span: SourceInfo, location: SourcePosition, document: &Path, interner: &Interner) -> bool {
   let span_begin = span.begin;
   let span_end = span.end;

   #[allow(clippy::if_same_then_else)]
   let in_range_of_span = if location.line > span_begin.line && location.line < span_end.line {
      // the line is entirely contained
      true
   } else if location.line > span_begin.line && location.line == span_end.line && location.col <= span_end.col {
      // the location is in the last line of the span
      true
   } else if location.line == span_begin.line && location.line < span_end.line && location.col >= span_begin.col {
      // the location is in the first line of the span
      true
   } else {
      // the span is single line and the location is in it
      location.line == span_begin.line
         && location.col >= span_begin.col
         && location.line == span_end.line
         && location.col <= span_end.col
   };

   if in_range_of_span {
      // now verify the document matches (allocates)
      let canon_path = roland_source_path_to_canon_path(&span.file, interner);
      canon_path
         .map(|x| x.map(|x| x == document).unwrap_or(false))
         .unwrap_or(false)
   } else {
      false
   }
}

#[must_use]
pub fn find_definition(sp: SourcePosition, document: &Path, ctx: &CompilationContext) -> Option<SourceInfo> {
   for expr in ctx.expressions.values.iter() {
      match &expr.expression {
         Expression::ProcedureCall { proc_name, .. } => {
            if !span_contains(proc_name.location, sp, document, &ctx.interner) {
               continue;
            }
            return ctx
               .program
               .procedure_info
               .get(&proc_name.identifier)
               .map(|x| x.location);
         }
         Expression::StructLiteral(struct_name, _) => {
            if !span_contains(struct_name.location, sp, document, &ctx.interner) {
               continue;
            }
            return ctx.program.struct_info.get(&struct_name.identifier).map(|x| x.location);
         }
         Expression::EnumLiteral(enum_name, _) => {
            if !span_contains(enum_name.location, sp, document, &ctx.interner) {
               continue;
            }
            return ctx.program.enum_info.get(&enum_name.identifier).map(|x| x.location);
         }
         _ => continue,
      }
   }

   None
}
