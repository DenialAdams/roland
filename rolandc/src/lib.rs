#![warn(clippy::pedantic)]
#![allow(clippy::explicit_iter_loop)] // I find explicit iter more readable
#![allow(clippy::match_same_arms)] // Sometimes I find this more clear (when it's just calling something)
#![allow(clippy::too_many_lines)] // A procedure should have however many lines as it needs. More procedures is not better.
#![allow(clippy::too_many_arguments)] // Similar to above, take the amount that you need
#![allow(clippy::flat_map_option)] // Not sure how filter_map is any more clear than flat_map
#![allow(clippy::cast_sign_loss)] // I am aware
#![allow(clippy::cast_possible_wrap)] // I am aware
#![allow(clippy::cast_possible_wrap)] // I am aware
#![allow(clippy::cast_possible_truncation)] // I am aware
#![allow(clippy::single_match_else)] // Not always an improvement in my opinion
#![allow(clippy::missing_errors_doc)] // Nothing is documented
#![allow(clippy::missing_panics_doc)] // Nothing is documented
#![allow(clippy::module_name_repetitions)] // I don't really care that much
#![allow(clippy::match_wildcard_for_single_variants)] // False positives
#![allow(clippy::new_without_default)] // I don't want dead code
#![allow(clippy::result_unit_err)] // This is based on a notion of public that doesn't really apply for me
#![feature(hash_drain_filter)]

mod add_virtual_variables;
mod compile_globals;
mod constant_folding;
mod disjoint_set;
pub mod error_handling;
pub mod interner;
mod lex;
pub mod parse;
mod semantic_analysis;
mod size_info;
pub mod source_info;
mod type_data;
mod typed_index_vec;
mod various_expression_lowering;
mod wasm;

use error_handling::error_handling_macros::{rolandc_error, rolandc_error_no_loc};
use error_handling::ErrorManager;
use indexmap::{IndexMap, IndexSet};
pub use parse::Program;
use parse::{ExpressionId, ExpressionNode, ExpressionPool, ImportNode};
use source_info::SourcePath;
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::path::{Path, PathBuf};
use typed_index_vec::HandleMap;

use crate::interner::Interner;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Target {
   Wasi,
   Wasm4,
   Microw8,
}

impl Display for Target {
   fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      match self {
         Target::Wasi => write!(f, "WASI"),
         Target::Wasm4 => write!(f, "WASM-4"),
         Target::Microw8 => write!(f, "Microw8"),
      }
   }
}

pub enum CompilationError {
   Lex,
   Parse,
   Semantic(u64),
   Io,
   Internal,
}

pub trait FileResolver<'a> {
   fn resolve_path(&mut self, path: &Path) -> std::io::Result<Cow<'a, str>>;
}

pub enum CompilationEntryPoint<'a, FR: FileResolver<'a>> {
   Playground(&'a str),
   PathResolving(PathBuf, FR),
}

// Repeated compilations can be sped up by reusing the context
pub struct CompilationContext {
   pub expressions: HandleMap<ExpressionId, ExpressionNode>,
   pub interner: Interner,
   pub err_manager: ErrorManager,
   pub program: Program,
}

impl CompilationContext {
   #[must_use]
   pub fn new() -> CompilationContext {
      CompilationContext {
         expressions: HandleMap::new(),
         interner: Interner::with_capacity(1024),
         err_manager: ErrorManager::new(),
         program: Program {
            external_procedures: Vec::new(),
            procedures: Vec::new(),
            enums: Vec::new(),
            structs: Vec::new(),
            consts: Vec::new(),
            statics: Vec::new(),
            literals: IndexSet::new(),
            struct_info: IndexMap::new(),
            static_info: IndexMap::new(),
            enum_info: IndexMap::new(),
            procedure_info: IndexMap::new(),
            struct_size_info: HashMap::new(),
         },
      }
   }
}

pub fn compile_for_errors<'a, FR: FileResolver<'a>>(
   ctx: &mut CompilationContext,
   user_program_ep: CompilationEntryPoint<'a, FR>,
   target: Target,
) -> Result<(), CompilationError> {
   ctx.expressions.clear();
   ctx.err_manager.clear();
   // We don't have to clear the interner - assumption is that the context is coming from a recent version of the same source, so symbols should be relevant

   ctx.program = match user_program_ep {
      CompilationEntryPoint::PathResolving(ep_path, mut resolver) => {
         let mut user_program = Program::new();
         let mut import_queue: Vec<PathBuf> = vec![ep_path];
         let mut imported_files = HashSet::new();
         while let Some(mut base_path) = import_queue.pop() {
            let canonical_path = match std::fs::canonicalize(&base_path) {
               Ok(p) => p,
               Err(e) => {
                  rolandc_error_no_loc!(
                     ctx.err_manager,
                     "Failed to canonicalize path '{}': {}",
                     base_path.as_os_str().to_string_lossy(),
                     e
                  );
                  return Err(CompilationError::Io);
               }
            };
            if imported_files.contains(&canonical_path) {
               continue;
            }
            imported_files.insert(canonical_path);

            let program_s = match resolver.resolve_path(&base_path) {
               Ok(s) => s,
               Err(e) => {
                  rolandc_error_no_loc!(
                     ctx.err_manager,
                     "Failed to read imported file '{}': {}",
                     base_path.as_os_str().to_string_lossy(),
                     e
                  );
                  return Err(CompilationError::Io);
               }
            };

            let mut parsed = lex_and_parse(
               &program_s,
               SourcePath::File(ctx.interner.intern(&base_path.as_os_str().to_string_lossy())),
               &mut ctx.err_manager,
               &mut ctx.interner,
               &mut ctx.expressions,
            )?;
            merge_program(&mut user_program, &mut parsed.1);

            base_path.pop(); // /foo/bar/main.rol -> /foo/bar
            for file in parsed.0.iter().map(|x| x.import_path) {
               let file_str = ctx.interner.lookup(file);
               let mut new_path = base_path.clone();
               new_path.push(file_str);
               import_queue.push(new_path);
            }
         }
         user_program
      }
      CompilationEntryPoint::Playground(contents) => {
         let (files_to_import, user_program) = lex_and_parse(
            contents,
            SourcePath::Sandbox,
            &mut ctx.err_manager,
            &mut ctx.interner,
            &mut ctx.expressions,
         )?;
         if !files_to_import.is_empty() {
            rolandc_error!(
               ctx.err_manager,
               files_to_import[0].location,
               "Can't import files in the Roland playground",
            );
            return Err(CompilationError::Io);
         }
         user_program
      }
   };

   let mut std_lib = match target {
      Target::Wasi => {
         let std_lib_s = include_str!("../../lib/wasi.rol");
         lex_and_parse(
            std_lib_s,
            SourcePath::Std,
            &mut ctx.err_manager,
            &mut ctx.interner,
            &mut ctx.expressions,
         )
      }
      Target::Wasm4 => {
         let std_lib_s = include_str!("../../lib/wasm4.rol");
         lex_and_parse(
            std_lib_s,
            SourcePath::Std,
            &mut ctx.err_manager,
            &mut ctx.interner,
            &mut ctx.expressions,
         )
      }
      Target::Microw8 => {
         let std_lib_s = include_str!("../../lib/microw8.rol");
         lex_and_parse(
            std_lib_s,
            SourcePath::Std,
            &mut ctx.err_manager,
            &mut ctx.interner,
            &mut ctx.expressions,
         )
      }
   }?;

   merge_program(&mut ctx.program, &mut std_lib.1);

   let std_lib_s = include_str!("../../lib/shared.rol");
   let mut shared_std = lex_and_parse(
      std_lib_s,
      SourcePath::Std,
      &mut ctx.err_manager,
      &mut ctx.interner,
      &mut ctx.expressions,
   )?;
   merge_program(&mut ctx.program, &mut shared_std.1);

   let mut err_count = semantic_analysis::type_and_procedure_info::populate_type_and_procedure_info(
      &mut ctx.program,
      &mut ctx.err_manager,
      &mut ctx.interner,
   );

   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   err_count = semantic_analysis::validator::type_and_check_validity(
      &mut ctx.program,
      &mut ctx.err_manager,
      &mut ctx.interner,
      &mut ctx.expressions,
      target,
   );

   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   err_count = compile_globals::compile_globals(
      &ctx.program,
      &mut ctx.expressions,
      &mut ctx.interner,
      &ctx.program.struct_size_info,
      &mut ctx.err_manager,
   );
   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   various_expression_lowering::lower_consts(&mut ctx.program, &mut ctx.expressions, &mut ctx.interner);

   err_count = compile_globals::ensure_statics_const(
      &ctx.program,
      &mut ctx.expressions,
      &mut ctx.interner,
      &mut ctx.err_manager,
   );

   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   err_count = constant_folding::fold_constants(
      &mut ctx.program,
      &mut ctx.err_manager,
      &mut ctx.expressions,
      &ctx.interner,
   );

   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   Ok(())
}

pub fn compile<'a, FR: FileResolver<'a>>(
   ctx: &mut CompilationContext,
   user_program_ep: CompilationEntryPoint<'a, FR>,
   target: Target,
) -> Result<Vec<u8>, CompilationError> {
   compile_for_errors(ctx, user_program_ep, target)?;

   // it would make sense to do this right after constants are lowered
   // however, we want to keep that information around for the language server
   ctx.program.static_info.retain(|_, v| !v.is_const);

   add_virtual_variables::add_virtual_vars(&mut ctx.program, &ctx.expressions);
   match target {
      Target::Wasi => Ok(wasm::emit_wasm(
         &mut ctx.program,
         &mut ctx.interner,
         &ctx.expressions,
         target,
      )),
      Target::Wasm4 | Target::Microw8 => {
         let wat = wasm::emit_wasm(&mut ctx.program, &mut ctx.interner, &ctx.expressions, target);
         let wasm = match wat::parse_bytes(&wat) {
            Ok(wasm_bytes) => wasm_bytes.into_owned(),
            Err(_) => return Err(CompilationError::Internal),
         };
         Ok(wasm)
      }
   }
}

fn merge_program(main_program: &mut Program, other_program: &mut Program) {
   main_program.literals.extend(other_program.literals.drain(0..));
   main_program
      .external_procedures
      .extend(other_program.external_procedures.drain(0..));
   main_program.procedures.extend(other_program.procedures.drain(0..));
   main_program.structs.extend(other_program.structs.drain(0..));
   main_program.statics.extend(other_program.statics.drain(0..));
   main_program.enums.extend(other_program.enums.drain(0..));
   main_program.consts.extend(other_program.consts.drain(0..));
}

fn lex_and_parse(
   s: &str,
   source_path: SourcePath,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
   expressions: &mut ExpressionPool,
) -> Result<(Vec<ImportNode>, Program), CompilationError> {
   let tokens = match lex::lex(s, source_path, err_manager, interner) {
      Err(()) => return Err(CompilationError::Lex),
      Ok(v) => v,
   };
   match parse::astify(tokens, err_manager, interner, expressions) {
      Err(()) => Err(CompilationError::Parse),
      Ok((imports, program)) => Ok((imports, program)),
   }
}
