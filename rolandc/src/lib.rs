#![warn(clippy::pedantic)]

// Clippy lints I don't like
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
#![allow(clippy::module_name_repetitions)] // I don't really care that much

// Clippy lints that cause false positives
#![allow(clippy::match_wildcard_for_single_variants)]

mod add_virtual_variables;
mod compile_globals;
mod constant_folding;
mod html_debug;
mod interner;
mod lex;
mod parse;
mod semantic_analysis;
mod size_info;
mod type_data;
mod typed_index_vec;
mod various_expression_lowering;
mod wasm;

use interner::StrId;
use parse::{ExpressionPool, Program};
use size_info::{calculate_struct_size_info, SizeInfo};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::io::Write;
use std::path::PathBuf;
use typed_index_vec::HandleMap;

use crate::interner::Interner;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Target {
   Wasi,
   Wasm4,
}

impl Display for Target {
   fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      match self {
         Target::Wasi => write!(f, "WASI"),
         Target::Wasm4 => write!(f, "WASM-4"),
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

pub fn compile<E: Write, A: Write>(
   user_program_s: &str,
   user_program_path: Option<PathBuf>,
   err_stream: &mut E,
   html_ast_out: Option<&mut A>,
   do_constant_folding: bool,
   target: Target,
) -> Result<Vec<u8>, CompilationError> {
   let mut interner = Interner::with_capacity(1024);

   let mut expressions = HandleMap::new();

   let mut imported_files = HashSet::new();
   if let Some(x) = user_program_path.as_ref() {
      let canonical_path = match std::fs::canonicalize(x) {
         Ok(p) => p,
         Err(e) => {
            writeln!(
               err_stream,
               "Failed to canonicalize path '{}': {}",
               x.as_os_str().to_string_lossy(),
               e
            )
            .unwrap();
            return Err(CompilationError::Io);
         }
      };
      imported_files.insert(canonical_path);
   }
   let root_source_location = user_program_path
      .as_ref()
      .map(|x| interner.intern(&x.to_string_lossy()));

   let (files_to_import, mut user_program) = lex_and_parse(
      user_program_s,
      root_source_location,
      err_stream,
      &mut interner,
      &mut expressions,
   )?;

   let mut base_path = user_program_path.unwrap_or_else(PathBuf::new);
   base_path.pop(); // /foo/bar/main.rol -> /foo/bar
   let mut import_queue: Vec<PathBuf> = vec![];

   for file in files_to_import {
      let file_str = interner.lookup(file);
      let mut new_path = base_path.clone();
      new_path.push(file_str);
      import_queue.push(new_path);
   }

   while let Some(mut base_path) = import_queue.pop() {
      let canonical_path = match std::fs::canonicalize(&base_path) {
         Ok(p) => p,
         Err(e) => {
            writeln!(
               err_stream,
               "Failed to canonicalize path '{}': {}",
               base_path.as_os_str().to_string_lossy(),
               e
            )
            .unwrap();
            return Err(CompilationError::Io);
         }
      };
      if imported_files.contains(&canonical_path) {
         continue;
      }
      imported_files.insert(canonical_path);

      let program_s = match std::fs::read_to_string(&base_path) {
         Ok(s) => s,
         Err(e) => {
            writeln!(
               err_stream,
               "Failed to read imported file '{}': {}",
               base_path.as_os_str().to_string_lossy(),
               e
            )
            .unwrap();
            return Err(CompilationError::Io);
         }
      };
      let mut parsed = lex_and_parse(
         &program_s,
         Some(interner.intern(&base_path.as_os_str().to_string_lossy())),
         err_stream,
         &mut interner,
         &mut expressions,
      )?;
      merge_program(&mut user_program, &mut parsed.1);

      base_path.pop(); // /foo/bar/main.rol -> /foo/bar
      for file in parsed.0.iter().copied() {
         let file_str = interner.lookup(file);
         let mut new_path = base_path.clone();
         new_path.push(file_str);
         import_queue.push(new_path);
      }
   }

   let num_procedures_before_std_merge = user_program.procedures.len();

   let std_source_info = Some(interner.intern("<std>"));
   let mut std_lib = match target {
      Target::Wasi => {
         let std_lib_s = include_str!("../../lib/wasi.rol");
         lex_and_parse(std_lib_s, std_source_info, err_stream, &mut interner, &mut expressions)
      }
      Target::Wasm4 => {
         let std_lib_s = include_str!("../../lib/wasm4.rol");
         lex_and_parse(std_lib_s, std_source_info, err_stream, &mut interner, &mut expressions)
      }
   }?;

   merge_program(&mut user_program, &mut std_lib.1);

   let std_lib_s = include_str!("../../lib/shared.rol");
   let mut shared_std = lex_and_parse(std_lib_s, std_source_info, err_stream, &mut interner, &mut expressions)?;
   merge_program(&mut user_program, &mut shared_std.1);

   let mut err_count = semantic_analysis::validator::type_and_check_validity(
      &mut user_program,
      err_stream,
      &mut interner,
      &mut expressions,
      target,
   );

   if err_count > 0 {
      if let Some(w) = html_ast_out {
         let mut program_without_std = user_program.clone();
         program_without_std.procedures.truncate(num_procedures_before_std_merge);
         html_debug::print_ast_as_html(w, &program_without_std, &mut interner, &expressions);
      }
      return Err(CompilationError::Semantic(err_count));
   }

   // We calculate this earlier than you might expect, because we need it for sizeof lowering
   let mut struct_size_info: HashMap<StrId, SizeInfo> = HashMap::with_capacity(user_program.struct_info.len());
   for s in user_program.struct_info.iter() {
      calculate_struct_size_info(
         *s.0,
         &user_program.enum_info,
         &user_program.struct_info,
         &mut struct_size_info,
      );
   }

   err_count = compile_globals::compile_globals(
      &user_program,
      &mut expressions,
      &mut interner,
      &struct_size_info,
      err_stream,
   );
   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   various_expression_lowering::lower_consts(&struct_size_info, &mut user_program, &mut expressions, &mut interner);
   user_program.static_info.retain(|_, v| !v.is_const);

   err_count = compile_globals::ensure_statics_const(&user_program, &mut expressions, &mut interner, err_stream);
   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   if do_constant_folding {
      err_count = constant_folding::fold_constants(&mut user_program, err_stream, &mut expressions, &interner);
   }

   if let Some(w) = html_ast_out {
      let mut program_without_std = user_program.clone();
      program_without_std.procedures.truncate(num_procedures_before_std_merge);
      html_debug::print_ast_as_html(w, &program_without_std, &mut interner, &expressions);
   }

   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   add_virtual_variables::add_virtual_vars(&mut user_program, &expressions);

   match target {
      Target::Wasi => Ok(wasm::emit_wasm(
         &struct_size_info,
         &mut user_program,
         &mut interner,
         &expressions,
         0,
         false,
      )),
      Target::Wasm4 => {
         let wat = wasm::emit_wasm(
            &struct_size_info,
            &mut user_program,
            &mut interner,
            &expressions,
            0x19a0,
            true,
         );
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

fn lex_and_parse<W: Write>(
   s: &str,
   source_path: Option<StrId>,
   err_stream: &mut W,
   interner: &mut Interner,
   expressions: &mut ExpressionPool,
) -> Result<(Vec<StrId>, Program), CompilationError> {
   let tokens = match lex::lex(s, source_path, err_stream, interner) {
      Err(()) => return Err(CompilationError::Lex),
      Ok(v) => v,
   };
   match parse::astify(tokens, err_stream, interner, expressions) {
      Err(()) => Err(CompilationError::Parse),
      Ok((imports, program)) => Ok((imports, program)),
   }
}
