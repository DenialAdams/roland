use std::path::Path;

use rolandc::CompilationContext;
use rolandc::interner::Interner;
use rolandc::parse::UserDefinedTypeId;
use rolandc::source_info::{SourceInfo, SourcePosition};
use rolandc::type_data::ExpressionType;

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
   for parsed_type in ctx.program.parsed_types.iter() {
      if !span_contains(parsed_type.location, sp, document, &ctx.interner) {
         continue;
      }

      if let ExpressionType::Unresolved {
         name: str,
         generic_args: _,
      } = parsed_type.e_type.get_type_or_type_being_pointed_to_recursively()
      {
         // These nodes should never be resolved
         return match ctx.program.user_defined_type_name_table.get(str) {
            Some(UserDefinedTypeId::Enum(x)) => ctx.program.user_defined_types.enum_info.get(*x).map(|x| x.location),
            Some(UserDefinedTypeId::Struct(x)) => {
               ctx.program.user_defined_types.struct_info.get(*x).map(|x| x.location)
            }
            Some(UserDefinedTypeId::Union(x)) => ctx.program.user_defined_types.union_info.get(*x).map(|x| x.location),
            // Limitation :\
            Some(UserDefinedTypeId::Alias(_)) => None,
            None => None,
         };
      }
   }

   for (source_span, definition_span) in ctx.program.source_to_definition.iter() {
      if span_contains(*source_span, sp, document, &ctx.interner) {
         return Some(*definition_span);
      }
   }

   None
}
