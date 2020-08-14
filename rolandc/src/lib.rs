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
   Sematic(u64),
}

pub fn compile<W: Write>(user_program_s: &str, html_ast_out: Option<&mut W>) -> Result<Vec<u8>, CompilationError> {
   let mut user_program = lex_and_parse(user_program_s);
   let std_lib_s = include_str!("../../lib/print.rol");
   let std_lib = lex_and_parse(std_lib_s);
   merge_programs(&mut user_program, &mut [std_lib]);
   let err_count = validator::type_and_check_validity(&mut user_program);
   if let Some(w) = html_ast_out {
      html_debug::print_ast_as_html(w, &user_program);
   }
   if err_count > 0 {
      return Err(CompilationError::Sematic(err_count));
   }
   Ok(wasm::emit_wasm(&user_program))
}

fn merge_programs(main_program: &mut Program, other_programs: &mut [Program]) {
   for program in other_programs {
      main_program.literals.extend(program.literals.drain());
      main_program.procedures.extend(program.procedures.drain(0..));
   }
}

fn lex_and_parse(s: &str) -> Program {
   let tokens = match lex::lex(&s) {
      Err(()) => std::process::exit(1),
      Ok(v) => v,
   };
   match parse::astify(tokens) {
      Err(()) => std::process::exit(1),
      Ok(v) => v,
   }
}
