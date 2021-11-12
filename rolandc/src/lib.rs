mod const_lowering;
mod constant_folding;
mod html_debug;
mod interner;
mod lex;
mod parse;
mod semantic_analysis;
mod type_data;
mod wasm;

use parse::Program;
use std::io::Write;

use crate::interner::Interner;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Target {
   Wasi,
   Wasm4,
}

impl Target {
   fn entry_point(self) -> &'static str {
      match self {
         Target::Wasi => "main",
         Target::Wasm4 => "start",
      }
   }
}

pub enum CompilationError {
   Lex,
   Parse,
   Semantic(u64),
}

pub fn compile<E: Write, A: Write>(
   user_program_s: &str,
   err_stream: &mut E,
   html_ast_out: Option<&mut A>,
   do_constant_folding: bool,
   target: Target,
) -> Result<Vec<u8>, CompilationError> {
   let mut interner = Interner::with_capacity(1024);

   let mut user_program = lex_and_parse(user_program_s, err_stream, &mut interner)?;
   let num_procedures_before_merge = user_program.procedures.len();

   match target {
      Target::Wasi => {
         let std_lib_s = include_str!("../../lib/print.rol");
         let std_lib = lex_and_parse(std_lib_s, err_stream, &mut interner)?;

         merge_programs(&mut user_program, &mut [std_lib]);
      }
      Target::Wasm4 => {
         let std_lib_s = include_str!("../../lib/wasm4.rol");
         let std_lib = lex_and_parse(std_lib_s, err_stream, &mut interner)?;

         merge_programs(&mut user_program, &mut [std_lib]);
      }
   }

   let mut err_count =
      semantic_analysis::validator::type_and_check_validity(&mut user_program, err_stream, &mut interner, target);

   if err_count == 0 {
      const_lowering::lower_consts(&mut user_program, err_stream);
      user_program.static_info.retain(|_, v| !v.is_const);

      if do_constant_folding {
         err_count = constant_folding::fold_constants(&mut user_program, err_stream);
      }
   }

   if let Some(w) = html_ast_out {
      let mut program_without_std = user_program.clone();
      program_without_std.procedures.truncate(num_procedures_before_merge);
      html_debug::print_ast_as_html(w, &program_without_std, &mut interner);
   }

   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   match target {
      Target::Wasi => Ok(wasm::emit_wasm(&mut user_program, &mut interner, 0, false)),
      Target::Wasm4 => {
         let wat = wasm::emit_wasm(&mut user_program, &mut interner, 0x19a0, true);
         Ok(wat::parse_bytes(&wat).unwrap().into_owned())
      }
   }
}

fn merge_programs(main_program: &mut Program, other_programs: &mut [Program]) {
   for program in other_programs {
      main_program.literals.extend(program.literals.drain());
      main_program.procedures.extend(program.procedures.drain(0..));
      main_program.structs.extend(program.structs.drain(0..));
      main_program.statics.extend(program.statics.drain(0..));
      main_program.enums.extend(program.enums.drain(0..));
      main_program.consts.extend(program.consts.drain(0..));
   }
}

fn lex_and_parse<W: Write>(s: &str, err_stream: &mut W, interner: &mut Interner) -> Result<Program, CompilationError> {
   let tokens = match lex::lex(s, err_stream, interner) {
      Err(()) => return Err(CompilationError::Lex),
      Ok(v) => v,
   };
   match parse::astify(tokens, err_stream, interner) {
      Err(()) => Err(CompilationError::Parse),
      Ok(v) => Ok(v),
   }
}
