use std::path::Path;

use rolandc::parse::UserDefinedTypeId;
use rolandc::source_info::{SourceInfo, SourcePosition};
use rolandc::type_data::ExpressionType;
use rolandc::{CompilationContext, FileMap};

use crate::roland_source_path_to_canon_path;

#[must_use]
fn span_contains(span: SourceInfo, location: SourcePosition, document: &Path, file_map: &FileMap) -> bool {
   let in_range_of_span = location.0 >= span.begin.0 && location.0 <= span.end.0;

   if in_range_of_span {
      // now verify the document matches (allocates)
      let canon_path = roland_source_path_to_canon_path(&span.file, file_map);
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
      if !span_contains(parsed_type.location, sp, document, &ctx.source_files) {
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
            Some(UserDefinedTypeId::Alias(x)) => ctx.program.user_defined_types.alias_info.get(*x).map(|x| x.location),
            None => None,
         };
      }
   }

   for (source_span, definition_span) in ctx.program.source_to_definition.iter() {
      if span_contains(*source_span, sp, document, &ctx.source_files) {
         return Some(*definition_span);
      }
   }

   None
}
