use std::borrow::Cow;
use std::collections::HashSet;
use std::path::PathBuf;

use include_dir::{Dir, include_dir};

use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_no_loc};
use crate::parse::{ImportNode, LinkNode};
use crate::source_info::{SourceInfo, SourcePath, SourcePosition};
use crate::{CompilationContext, FileResolver, lex_and_parse};

static STDLIB_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/../lib");

pub struct StdFileResolver;

impl<'a> FileResolver<'a> for StdFileResolver {
   const IS_STD: bool = true;
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      Ok(Cow::Borrowed(
         STDLIB_DIR
            .get_file(path)
            .ok_or_else(|| {
               std::io::Error::new(
                  std::io::ErrorKind::NotFound,
                  "The standard library doesn't contain that file",
               )
            })?
            .contents_utf8()
            .unwrap(),
      ))
   }
}

pub fn import_program<'a, FR: FileResolver<'a>>(
   ctx: &mut CompilationContext,
   links: &mut Vec<LinkNode>,
   path: PathBuf,
   mut resolver: FR,
) -> Result<(), ()> {
   let mut import_queue: Vec<(PathBuf, Option<ImportNode>)> = vec![(path, None)];

   let mut imported_files = HashSet::new();
   while let Some(pair) = import_queue.pop() {
      let mut base_path = pair.0;
      let import_location = pair.1;
      let canonical_path = if FR::IS_STD {
         base_path.clone()
      } else {
         match std::fs::canonicalize(&base_path) {
            Ok(p) => p,
            Err(e) => {
               if let Some(l) = import_location {
                  rolandc_error!(
                     ctx.err_manager,
                     l.import_path.location,
                     "Failed to canonicalize path '{}': {}",
                     base_path.as_os_str().to_string_lossy(),
                     e
                  );
               } else {
                  rolandc_error_no_loc!(
                     ctx.err_manager,
                     "Failed to canonicalize path '{}': {}",
                     base_path.as_os_str().to_string_lossy(),
                     e
                  );
               }
               return Err(());
            }
         }
      };
      if !imported_files.insert(canonical_path) {
         continue;
      }

      let program_s = match resolver.resolve_path(&base_path) {
         Ok(s) => s,
         Err(e) => {
            if let Some(l) = import_location {
               rolandc_error!(
                  ctx.err_manager,
                  l.import_path.location,
                  "Failed to read imported file '{}': {}",
                  base_path.as_os_str().to_string_lossy(),
                  e
               );
            } else {
               rolandc_error_no_loc!(
                  ctx.err_manager,
                  "Failed to read imported file '{}': {}",
                  base_path.as_os_str().to_string_lossy(),
                  e
               );
            }
            return Err(());
         }
      };

      let source_path = if FR::IS_STD {
         SourcePath::Std(ctx.interner.intern(&base_path.as_os_str().to_string_lossy()))
      } else {
         SourcePath::File(ctx.interner.intern(&base_path.as_os_str().to_string_lossy()))
      };

      if let Some(il) = import_location {
         let dummy_sp = SourcePosition { line: 0, col: 0 };
         ctx.program.source_to_definition.insert(
            il.import_path.location,
            SourceInfo {
               begin: dummy_sp,
               end: dummy_sp,
               file: source_path,
            },
         );
      }

      let imports = lex_and_parse(
         &program_s,
         source_path,
         &mut ctx.err_manager,
         &mut ctx.interner,
         &mut ctx.program,
         links,
      )?;

      base_path.pop(); // /foo/bar/main.rol -> /foo/bar
      for file in imports {
         let file_str = ctx.interner.lookup(file.import_path.str);
         if let Some(std_path) = file_str.strip_prefix("std:") {
            import_program(ctx, links, std_path.into(), StdFileResolver)?;
            continue;
         }
         let mut new_path = base_path.clone();
         new_path.push(file_str);
         import_queue.push((new_path, Some(file)));
      }
   }

   Ok(())
}
