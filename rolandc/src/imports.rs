use std::borrow::Cow;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam::channel::Select;
use include_dir::{Dir, include_dir};
use parking_lot::Mutex;

use crate::error_handling::SharedErrorManager;
use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_no_loc};
use crate::lex::Lexer;
use crate::parse::{self, LinkNode, ParseResult};
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
   import_location: Option<SourceInfo>,
   is_std: bool,
}

pub struct NewImportSender<'a> {
   sender: crossbeam::channel::Sender<ImportQueueNode>,
   in_flight_count: &'a AtomicUsize,
   currently_parsing_std: bool,
   currently_parsing_path: PathBuf,
}

impl NewImportSender<'_> {
   pub fn send(&self, import_str: &str, import_location: SourceInfo) {
      self.in_flight_count.fetch_add(1, Ordering::Relaxed);
      let (new_path, is_std) = if let Some(std_path) = import_str.strip_prefix("std:") {
         (std_path.into(), true)
      } else {
         (
            self
               .currently_parsing_path
               .parent()
               .map_or_else(|| self.currently_parsing_path.clone(), |parent| parent.join(import_str)),
            self.currently_parsing_std,
         )
      };
      let _ = self.sender.send(ImportQueueNode {
         path: new_path,
         import_location: Some(import_location),
         is_std,
      });
   }
}

pub fn import_program(
   ctx: &mut CompilationContext,
   links: &mut Vec<LinkNode>,
   path: PathBuf,
   user_resolver: &mut dyn FileResolver,
   config: &CompilationConfig,
) -> Result<(), ()> {
   let (import_queue_tx, import_queue_rx) = crossbeam::channel::unbounded();

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
      import_queue_tx
         .send(ImportQueueNode {
            path: std_lib_start_path,
            import_location: None,
            is_std: true,
         })
         .unwrap();
   }

   import_queue_tx
      .send(ImportQueueNode {
         path,
         import_location: None,
         is_std: false,
      })
      .unwrap();

   let err_manager = SharedErrorManager::new(&mut ctx.err_manager);
   let global_exprs = Mutex::new(&mut ctx.program.global_exprs);

   let (lex_parse_results_tx, lex_parse_results_rx) = crossbeam::channel::unbounded();

   let num_in_flight: AtomicUsize = AtomicUsize::new(1 + usize::from(config.include_std));

   {
      let interner = &ctx.interner;
      let err_manager = &err_manager;
      let source_files = &mut ctx.source_files;
      let global_exprs = &global_exprs;
      let p_source_to_definition = &mut ctx.program.source_to_definition;
      let p_procedures = &mut ctx.program.procedures;
      let p_procedure_bodies = &mut ctx.program.procedure_bodies;
      let p_structs = &mut ctx.program.structs;
      let p_unions = &mut ctx.program.unions;
      let p_enums = &mut ctx.program.enums;
      let p_type_aliases = &mut ctx.program.type_aliases;
      let p_consts = &mut ctx.program.consts;
      let p_statics = &mut ctx.program.statics;
      let p_parsed_types = &mut ctx.program.parsed_types;
      let num_in_flight = &num_in_flight;

      rayon::in_place_scope(move |s| {
         let mut select = Select::new();
         select.recv(&import_queue_rx);
         select.recv(&lex_parse_results_rx);

         while num_in_flight.load(Ordering::Relaxed) > 0 {
            let op = select.select();
            if op.index() == 0 {
               let node = op.recv(&import_queue_rx).unwrap();

               let resolver = if node.is_std {
                  &mut std_resolver
               } else {
                  &mut *user_resolver
               };

               let canonical_path = if resolver.requires_canonicalization() {
                  match std::fs::canonicalize(&node.path) {
                     Ok(p) => p,
                     Err(e) => {
                        if let Some(l) = node.import_location {
                           rolandc_error!(
                              err_manager,
                              l,
                              "Failed to canonicalize path '{}': {}",
                              node.path.as_os_str().to_string_lossy(),
                              e
                           );
                        } else {
                           rolandc_error_no_loc!(
                              err_manager,
                              "Failed to canonicalize path '{}': {}",
                              node.path.as_os_str().to_string_lossy(),
                              e
                           );
                        }
                        return Err(());
                     }
                  }
               } else {
                  node.path.clone()
               };

               // TODO: fix this using some form of raw entry so we only clone canonical_path when we have to
               let (source_path, program_s) = match source_files.entry((canonical_path.clone(), node.is_std)) {
                  indexmap::map::Entry::Occupied(_) => {
                     num_in_flight.fetch_sub(1, Ordering::Relaxed);
                     continue;
                  }
                  indexmap::map::Entry::Vacant(vacant_entry) => {
                     let program_s = match resolver.resolve_path(&canonical_path) {
                        Ok(s) => s,
                        Err(e) => {
                           if let Some(l) = node.import_location {
                              rolandc_error!(
                                 err_manager,
                                 l,
                                 "Failed to read imported file '{}': {}",
                                 canonical_path.as_os_str().to_string_lossy(),
                                 e
                              );
                           } else {
                              rolandc_error_no_loc!(
                                 err_manager,
                                 "Failed to read imported file '{}': {}",
                                 canonical_path.as_os_str().to_string_lossy(),
                                 e
                              );
                           }
                           return Err(());
                        }
                     };
                     (SourcePath(vacant_entry.index()), vacant_entry.insert(program_s))
                  }
               };

               if let Some(il) = node.import_location {
                  let dummy_sp = SourcePosition(0);
                  p_source_to_definition.insert(
                     il,
                     SourceInfo {
                        begin: dummy_sp,
                        end: dummy_sp,
                        file: source_path,
                     },
                  );
               }

               {
                  let program_s: &str = program_s.as_ref();
                  // Extend the lifetime of the reference. This is safe as long as we don't free
                  // the program string buffer while this task is running.
                  let program_s: &str = unsafe { &*std::ptr::from_ref::<str>(program_s) };
                  let lex_parse_results_tx = lex_parse_results_tx.clone();
                  let import_sender = NewImportSender {
                     sender: import_queue_tx.clone(),
                     in_flight_count: num_in_flight,
                     currently_parsing_std: node.is_std,
                     currently_parsing_path: node.path,
                  };
                  s.spawn(move |_| {
                     // try block would be nicer here
                     let res = (move || -> Result<ParseResult, ()> {
                        let tokens = lex::lex_for_tokens(program_s, source_path, err_manager, interner)?;
                        Ok(parse::astify(
                           Lexer::from_tokens(tokens, source_path),
                           err_manager,
                           interner,
                           global_exprs,
                           &import_sender,
                        ))
                     })();
                     let _ = lex_parse_results_tx.send(res);
                  });
               }
            } else if op.index() == 1 {
               let lp_res = op.recv(&lex_parse_results_rx).unwrap();
               let Ok(mut parse_result) = lp_res else {
                  num_in_flight.fetch_sub(1, Ordering::Relaxed);
                  continue;
               };

               for parsed_proc in parse_result.items.procedures.drain(..) {
                  let id = p_procedures.insert(parsed_proc.proc);
                  if let Some(body) = parsed_proc.body {
                     p_procedure_bodies.insert(id, body);
                  }
               }

               p_structs.append(&mut parse_result.items.structs);
               p_unions.append(&mut parse_result.items.unions);
               p_enums.append(&mut parse_result.items.enums);
               p_type_aliases.append(&mut parse_result.items.type_aliases);
               p_consts.append(&mut parse_result.items.consts);
               p_statics.append(&mut parse_result.items.statics);
               p_parsed_types.append(&mut parse_result.parsed_types);
               links.append(&mut parse_result.items.links);

               num_in_flight.fetch_sub(1, Ordering::Relaxed);
            }
         }

         Ok(())
      })
   }
}
