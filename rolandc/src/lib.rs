#![warn(clippy::pedantic)]
#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
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
#![allow(clippy::needless_bitwise_bool)] // Sometimes I just don't want branches, man
#![allow(clippy::let_underscore_untyped)] // looks weird with no let
#![feature(hash_drain_filter)]

mod add_virtual_variables;
mod compile_consts;
mod constant_folding;
mod disjoint_set;
pub mod error_handling;
mod imports;
pub mod interner;
mod lex;
mod monomorphization;
pub mod parse;
mod pre_wasm_lowering;
mod semantic_analysis;
mod size_info;
pub mod source_info;
pub mod type_data;
mod typed_index_vec;
mod wasm;

use std::borrow::Cow;
use std::fmt::Display;
use std::path::{Path, PathBuf};

use error_handling::error_handling_macros::rolandc_error;
use error_handling::ErrorManager;
use interner::Interner;
pub use parse::Program;
use parse::{ExpressionId, ExpressionNode, ExpressionPool, ImportNode};
use source_info::SourcePath;
use typed_index_vec::HandleMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Target {
   Wasi,
   Wasm4,
   Microw8,
   Lib,
}

impl Display for Target {
   fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      match self {
         Target::Wasi => write!(f, "WASI"),
         Target::Wasm4 => write!(f, "WASM-4"),
         Target::Microw8 => write!(f, "Microw8"),
         Target::Lib => write!(f, "lib"),
      }
   }
}

pub enum CompilationError {
   Lex,
   Parse,
   Semantic,
   Io,
}

pub trait FileResolver<'a> {
   fn resolve_path(&mut self, path: &Path) -> std::io::Result<Cow<'a, str>>;
   const IS_STD: bool = false;
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
         program: Program::new(),
      }
   }
}

pub fn compile_for_errors<'a, FR: FileResolver<'a>>(
   ctx: &mut CompilationContext,
   user_program_ep: CompilationEntryPoint<'a, FR>,
   config: &CompilationConfig,
) -> Result<(), CompilationError> {
   ctx.program.clear();
   ctx.expressions.clear();
   ctx.err_manager.clear();
   // We don't have to clear the interner - assumption is that the context is coming from a recent version of the same source, so symbols should be relevant

   let std_lib_start_path: PathBuf = match config.target {
      Target::Wasi => "wasi.rol",
      Target::Wasm4 => "wasm4.rol",
      Target::Microw8 => "microw8.rol",
      Target::Lib => "shared.rol",
   }
   .into();

   if config.include_std {
      imports::import_program(ctx, std_lib_start_path, imports::StdFileResolver)?;
   }

   match user_program_ep {
      CompilationEntryPoint::PathResolving(ep_path, resolver) => {
         imports::import_program(ctx, ep_path, resolver)?;
      }
      CompilationEntryPoint::Playground(contents) => {
         let (files_to_import, mut user_program) = lex_and_parse(
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
         merge_program(&mut ctx.program, &mut user_program);
      }
   };

   semantic_analysis::type_and_procedure_info::populate_type_and_procedure_info(
      &mut ctx.program,
      &mut ctx.err_manager,
      &mut ctx.interner,
      config,
   );

   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }

   semantic_analysis::validator::type_and_check_validity(
      &mut ctx.program,
      &mut ctx.err_manager,
      &mut ctx.interner,
      &mut ctx.expressions,
      config.target,
   );

   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }

   compile_consts::compile_consts(
      &ctx.program,
      &mut ctx.expressions,
      &mut ctx.interner,
      &ctx.program.struct_size_info,
      &mut ctx.err_manager,
   );
   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }

   monomorphization::monomorphize(
      &mut ctx.program,
      &mut ctx.expressions,
      &mut ctx.interner,
      &mut ctx.err_manager,
   );
   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }
   ctx.program
      .procedures
      .retain(|x| x.definition.generic_parameters.is_empty());

   constant_folding::fold_constants(
      &mut ctx.program,
      &mut ctx.err_manager,
      &mut ctx.expressions,
      &ctx.interner,
   );
   ctx.program.global_info.retain(|_, v| !v.is_const);

   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }

   Ok(())
}

pub struct CompilationConfig {
   pub target: Target,
   pub include_std: bool,
   pub i_am_std: bool,
}

pub fn compile<'a, FR: FileResolver<'a>>(
   ctx: &mut CompilationContext,
   user_program_ep: CompilationEntryPoint<'a, FR>,
   config: &CompilationConfig,
) -> Result<Vec<u8>, CompilationError> {
   compile_for_errors(ctx, user_program_ep, config)?;

   pre_wasm_lowering::lower_enums_and_pointers(&mut ctx.program, &mut ctx.expressions);

   add_virtual_variables::add_virtual_vars(&mut ctx.program, &mut ctx.expressions);
   Ok(wasm::emit_wasm(
      &mut ctx.program,
      &mut ctx.interner,
      &ctx.expressions,
      config.target,
   ))
}

fn lex_and_parse(
   s: &str,
   source_path: SourcePath,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
   expressions: &mut ExpressionPool,
) -> Result<(Vec<ImportNode>, Program), CompilationError> {
   let Ok(tokens) = lex::lex(s, source_path, err_manager, interner) else {
      return Err(CompilationError::Lex)
   };
   match parse::astify(tokens, err_manager, interner, expressions) {
      Err(()) => Err(CompilationError::Parse),
      Ok((imports, program)) => Ok((imports, program)),
   }
}

fn merge_program(main_program: &mut Program, other_program: &mut Program) {
   main_program.literals.extend(other_program.literals.drain(..));
   main_program
      .external_procedures
      .append(&mut other_program.external_procedures);
   main_program.procedures.append(&mut other_program.procedures);
   main_program.structs.append(&mut other_program.structs);
   main_program.statics.append(&mut other_program.statics);
   main_program.enums.append(&mut other_program.enums);
   main_program.consts.append(&mut other_program.consts);
   main_program.parsed_types.append(&mut other_program.parsed_types);
}
