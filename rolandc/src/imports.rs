use std::borrow::Cow;
use std::collections::HashSet;
use std::path::PathBuf;

use include_dir::{include_dir, Dir};

use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_no_loc};
use crate::source_info::{SourceInfo, SourcePath};
use crate::{lex_and_parse, CompilationContext, CompilationError, FileResolver, merge_program};

static STDLIB_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/../lib");

pub struct StdFileResolver;

impl<'a> FileResolver<'a> for StdFileResolver {
   const IS_STD: bool = true;
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      Ok(Cow::Borrowed(
         STDLIB_DIR.get_file(path).unwrap().contents_utf8().unwrap(),
      ))
   }
}

pub fn import_program<'a, FR: FileResolver<'a>>(ctx: &mut CompilationContext, path: PathBuf, mut resolver: FR) -> Result<(), CompilationError> {
   let mut import_queue: Vec<(PathBuf, Option<SourceInfo>)> = vec![(path, None)];

   let mut imported_files = HashSet::new();
   while let Some(pair) = import_queue.pop() {
      let mut base_path = pair.0;
      let location = pair.1;
      let canonical_path = if FR::IS_STD {
         base_path.clone()
      } else {
         match std::fs::canonicalize(&base_path) {
            Ok(p) => p,
            Err(e) => {
               if let Some(l) = location {
                  rolandc_error!(
                     ctx.err_manager,
                     l,
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
               return Err(CompilationError::Io);
            }
         }
      };
      if !imported_files.insert(canonical_path) {
         continue;
      }

      let program_s = match resolver.resolve_path(&base_path) {
         Ok(s) => s,
         Err(e) => {
            if let Some(l) = location {
               rolandc_error!(
                  ctx.err_manager,
                  l,
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
            return Err(CompilationError::Io);
         }
      };

      let source_path = if FR::IS_STD {
         SourcePath::Std(ctx.interner.intern(&base_path.as_os_str().to_string_lossy()))
      } else {
         SourcePath::File(ctx.interner.intern(&base_path.as_os_str().to_string_lossy()))
      };

      let mut parsed = lex_and_parse(
         &program_s,
         source_path,
         &mut ctx.err_manager,
         &mut ctx.interner,
         &mut ctx.expressions,
      )?;
      merge_program(&mut ctx.program, &mut parsed.1);

      base_path.pop(); // /foo/bar/main.rol -> /foo/bar
      for file in parsed.0.iter() {
         let file_str = ctx.interner.lookup(file.import_path);
         let mut new_path = base_path.clone();
         new_path.push(file_str);
         import_queue.push((new_path, Some(file.location)));
      }
   }

   Ok(())
}
