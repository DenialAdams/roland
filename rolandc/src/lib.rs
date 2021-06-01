mod html_debug;
mod lex;
mod parse;
mod type_data;
mod validator;
mod wasm;

use parse::Program;
use std::io::Write;

pub enum CompilationError {
   Lex,
   Parse,
   Semantic(u64),
}

pub fn compile<E: Write, A: Write>(
   user_program_s: &str,
   err_stream: &mut E,
   html_ast_out: Option<&mut A>,
) -> Result<Vec<u8>, CompilationError> {
   let mut user_program = lex_and_parse(user_program_s, err_stream)?;
   let std_lib_s = include_str!("../../lib/print.rol");
   let std_lib = lex_and_parse(std_lib_s, err_stream)?;
   let num_procedures_before_merge = user_program.procedures.len();
   merge_programs(&mut user_program, &mut [std_lib]);
   let err_count = validator::type_and_check_validity(&mut user_program, err_stream);
   if let Some(w) = html_ast_out {
      let mut program_without_std = user_program.clone();
      program_without_std.procedures.truncate(num_procedures_before_merge);
      html_debug::print_ast_as_html(w, &program_without_std);
   }
   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }
   Ok(wasm::emit_wasm(&user_program))
}

fn merge_programs(main_program: &mut Program, other_programs: &mut [Program]) {
   for program in other_programs {
      main_program.literals.extend(program.literals.drain());
      main_program.procedures.extend(program.procedures.drain(0..));
      main_program.structs.extend(program.structs.drain(0..));
   }
}

fn lex_and_parse<W: Write>(s: &str, err_stream: &mut W) -> Result<Program, CompilationError> {
   let tokens = match lex::lex(&s, err_stream) {
      Err(()) => return Err(CompilationError::Lex),
      Ok(v) => v,
   };
   match parse::astify(tokens, err_stream) {
      Err(()) => Err(CompilationError::Parse),
      Ok(v) => Ok(v),
   }
}
