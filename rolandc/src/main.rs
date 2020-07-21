mod html_debug;
mod lex;
mod parse;
mod validator;
mod wasm;

use clap::Clap;
use parse::Program;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

#[derive(Clap)]
struct Opts {
   source_file: PathBuf,
   #[clap(long)]
   output_html_ast: bool,
   #[clap(short, long)]
   output: PathBuf,
}

fn main() {
   let mut opts: Opts = Opts::parse();
   let user_program_s = std::fs::read_to_string(opts.source_file).unwrap();
   let mut user_program = lex_and_parse(&user_program_s);
   let std_lib_s = include_str!("../../lib/print.rol");
   let std_lib = lex_and_parse(std_lib_s);
   merge_programs(&mut user_program, &mut [std_lib]);
   let err_count = validator::type_and_check_validity(&mut user_program);
   if opts.output_html_ast {
      html_debug::print_ast_as_html(&user_program);
   }
   if err_count > 0 {
      eprintln!("There were {} semantic errors, bailing", err_count);
      std::process::exit(1);
   }
   let wasm_text = wasm::emit_wasm(&user_program);
   //let wasm_bin = wabt::wat2wasm(wasm_text).unwrap();
   opts.output.set_extension("wast");
   let mut wasm_out = File::create(opts.output).unwrap();
   wasm_out.write_all(&wasm_text).unwrap();
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
