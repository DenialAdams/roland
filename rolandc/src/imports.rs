use std::borrow::Cow;
use std::path::PathBuf;

use include_dir::{Dir, include_dir};

use crate::error_handling::SharedErrorManager;
use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_no_loc};
use crate::lex::{Lexer, SourceToken};
use crate::parse::{self, ImportNode, LinkNode};
use crate::source_info::{SourceInfo, SourcePath, SourcePosition};
use crate::{CompilationConfig, CompilationContext, FileResolver, Target, lex};

static STDLIB_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/../lib");

pub struct StdFileResolver;

impl FileResolver for StdFileResolver {
   fn requires_canonicalization(&self) -> bool {
      false
   }
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'static, str>> {
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

struct ImportQueueNode {
   path: PathBuf,
   import: Option<ImportNode>,
   is_std: bool,
}

pub fn import_program(
   ctx: &mut CompilationContext,
   links: &mut Vec<LinkNode>,
   path: PathBuf,
   user_resolver: &mut dyn FileResolver,
   config: &CompilationConfig,
) -> Result<(), ()> {
   let mut import_queue: Vec<ImportQueueNode> = Vec::new();

   let mut std_resolver = StdFileResolver {};

   if config.include_std {
      let std_lib_start_path: PathBuf = match config.target {
         Target::Wasi => "wasi.rol",
         Target::Wasm4 => "wasm4.rol",
         Target::Microw8 => "microw8.rol",
         Target::Generic => "shared.rol",
         Target::QbeFreestanding | Target::QbeHost => "amd64.rol",
      }
      .into();
      import_queue.push(ImportQueueNode {
         path: std_lib_start_path,
         import: None,
         is_std: true,
      });
   }

   import_queue.push(ImportQueueNode {
      path,
      import: None,
      is_std: false,
   });

   let err_manager = SharedErrorManager::new(&mut ctx.err_manager);

   while let Some(node) = import_queue.pop() {
      let base_path = node.path;
      let import_location = node.import;
      let resolver = if node.is_std {
         &mut std_resolver
      } else {
         &mut *user_resolver
      };
      let canonical_path = if resolver.requires_canonicalization() {
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
      } else {
         base_path.clone()
      };

      let source_path: SourcePath;
      // TODO: fix this using some form of raw entry so we only clone canonical_path when we have to
      let program_s = match ctx.source_files.entry((canonical_path.clone(), node.is_std)) {
         indexmap::map::Entry::Occupied(_) => continue,
         indexmap::map::Entry::Vacant(vacant_entry) => {
            let program_s = match resolver.resolve_path(&canonical_path) {
               Ok(s) => s,
               Err(e) => {
                  if let Some(l) = import_location {
                     rolandc_error!(
                        ctx.err_manager,
                        l.import_path.location,
                        "Failed to read imported file '{}': {}",
                        canonical_path.as_os_str().to_string_lossy(),
                        e
                     );
                  } else {
                     rolandc_error_no_loc!(
                        ctx.err_manager,
                        "Failed to read imported file '{}': {}",
                        canonical_path.as_os_str().to_string_lossy(),
                        e
                     );
                  }
                  return Err(());
               }
            };
            source_path = SourcePath(vacant_entry.index());
            vacant_entry.insert(program_s)
         }
      };

      if let Some(il) = import_location {
         let dummy_sp = SourcePosition(0);
         ctx.program.source_to_definition.insert(
            il.import_path.location,
            SourceInfo {
               begin: dummy_sp,
               end: dummy_sp,
               file: source_path,
            },
         );
      }

      let tokens = lex::lex_for_tokens(program_s, source_path, &err_manager, &ctx.interner)?;
      let new_imports = parse::astify(
         Lexer::from_tokens(tokens, source_path),
         &err_manager,
         &ctx.interner,
         &mut ctx.program,
         links,
      );

      for file in new_imports {
         let file_str = ctx.interner.lookup(file.import_path.str);
         let (new_path, is_std) = if let Some(std_path) = file_str.strip_prefix("std:") {
            (std_path.into(), true)
         } else {
            (base_path.parent().unwrap().join(file_str), node.is_std)
         };
         import_queue.push(ImportQueueNode {
            path: new_path,
            import: Some(file),
            is_std,
         });
      }
   }

   Ok(())
}
