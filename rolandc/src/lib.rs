mod const_lowering;
mod constant_folding;
mod html_debug;
mod interner;
mod lex;
mod parse;
mod semantic_analysis;
mod type_data;
mod wasm;

use lex::{SourceInfo, SourceToken};
use parse::Program;
use std::fmt::Display;
use std::io::Write;

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

pub fn compile_for_fuzzer<E: Write, A: Write>(
   user_program: &[u8],
   err_stream: &mut E,
   html_ast_out: Option<&mut A>,
   do_constant_folding: bool,
   target: Target,
) -> Result<Vec<u8>, CompilationError> {
   let mut interner = Interner::with_capacity(1024);
   let an_ident = interner.intern("");
   let a_literal = interner.intern("");

   let mut tokens = Vec::with_capacity(user_program.len());
   for byte in user_program {
      let byte_in_range = byte % 56;

      let token = match byte_in_range {
         0 => lex::Token::Arrow,
         1 => lex::Token::KeywordElse,
         2 => lex::Token::KeywordIf,
         3 => lex::Token::KeywordProcedureDef,
         4 => lex::Token::KeywordStructDef,
         5 => lex::Token::KeywordEnumDef,
         6 => lex::Token::KeywordLet,
         7 => lex::Token::KeywordReturn,
         8 => lex::Token::KeywordLoop,
         9 => lex::Token::KeywordContinue,
         10 => lex::Token::KeywordBreak,
         11 => lex::Token::KeywordExtend,
         12 => lex::Token::KeywordTruncate,
         13 => lex::Token::KeywordTransmute,
         14 => lex::Token::KeywordConst,
         15 => lex::Token::KeywordStatic,
         16 => lex::Token::KeywordNamed,
         17 => lex::Token::KeywordAnd,
         18 => lex::Token::KeywordOr,
         19 => lex::Token::KeywordFor,
         20 => lex::Token::KeywordIn,
         21 => lex::Token::OpenBrace,
         22 => lex::Token::CloseBrace,
         23 => lex::Token::OpenParen,
         24 => lex::Token::CloseParen,
         25 => lex::Token::OpenSquareBracket,
         26 => lex::Token::CloseSquareBracket,
         27 => lex::Token::DoubleColon,
         28 => lex::Token::Colon,
         29 => lex::Token::Caret,
         30 => lex::Token::Amp,
         31 => lex::Token::Pipe,
         32 => lex::Token::Semicolon,
         33 => lex::Token::Identifier(an_ident),
         34 => lex::Token::BoolLiteral(true),
         35 => lex::Token::StringLiteral(a_literal),
         36 => lex::Token::IntLiteral(0),
         37 => lex::Token::FloatLiteral(0.0),
         38 => lex::Token::Plus,
         39 => lex::Token::Minus,
         40 => lex::Token::MultiplyDeref,
         41 => lex::Token::Divide,
         42 => lex::Token::Remainder,
         43 => lex::Token::Assignment,
         44 => lex::Token::Equality,
         45 => lex::Token::NotEquality,
         46 => lex::Token::LessThan,
         47 => lex::Token::LessThanOrEqualTo,
         48 => lex::Token::GreaterThan,
         49 => lex::Token::GreaterThanOrEqualTo,
         50 => lex::Token::ShiftLeft,
         51 => lex::Token::ShiftRight,
         52 => lex::Token::Comma,
         53 => lex::Token::Exclam,
         54 => lex::Token::Period,
         55 => lex::Token::DoublePeriod,
         _ => unreachable!(),
      };

      tokens.push(SourceToken {
         token,
         source_info: SourceInfo { line: 0, col: 0 },
      });
   }

   let user_program = parse::astify(tokens, err_stream, &interner).map_err(|()| CompilationError::Parse)?;
   compile_program(
      user_program,
      err_stream,
      html_ast_out,
      do_constant_folding,
      target,
      &mut interner,
   )
}

pub fn compile<E: Write, A: Write>(
   user_program_s: &str,
   err_stream: &mut E,
   html_ast_out: Option<&mut A>,
   do_constant_folding: bool,
   target: Target,
) -> Result<Vec<u8>, CompilationError> {
   let mut interner = Interner::with_capacity(1024);

   let user_program = parse_user_program(user_program_s, err_stream, &mut interner)?;

   compile_program(
      user_program,
      err_stream,
      html_ast_out,
      do_constant_folding,
      target,
      &mut interner,
   )
}

fn compile_program<E: Write, A: Write>(
   mut user_program: Program,
   err_stream: &mut E,
   html_ast_out: Option<&mut A>,
   do_constant_folding: bool,
   target: Target,
   interner: &mut Interner,
) -> Result<Vec<u8>, CompilationError> {
   let num_procedures_before_merge = user_program.procedures.len();

   let std_lib = match target {
      Target::Wasi => {
         let std_lib_s = include_str!("../../lib/print.rol");
         lex_and_parse(std_lib_s, err_stream, interner)
      }
      Target::Wasm4 => {
         let std_lib_s = include_str!("../../lib/wasm4.rol");
         lex_and_parse(std_lib_s, err_stream, interner)
      }
   }?;

   merge_programs(&mut user_program, &mut [std_lib]);

   let mut err_count =
      semantic_analysis::validator::type_and_check_validity(&mut user_program, err_stream, interner, target);

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
      html_debug::print_ast_as_html(w, &program_without_std, interner);
   }

   if err_count > 0 {
      return Err(CompilationError::Semantic(err_count));
   }

   match target {
      Target::Wasi => Ok(wasm::emit_wasm(&mut user_program, interner, 0, false)),
      Target::Wasm4 => {
         let wat = wasm::emit_wasm(&mut user_program, interner, 0x19a0, true);
         Ok(wat::parse_bytes(&wat).unwrap().into_owned())
      }
   }
}

#[cfg(fuzzing)]
fn parse_user_program<W: Write>(
   user_program_s: &str,
   err_stream: &mut W,
   interner: &mut Interner,
) -> Result<Program, CompilationError> {
   stacker::grow(33554432, || lex_and_parse(user_program_s, err_stream, interner))
}

#[cfg(not(fuzzing))]
fn parse_user_program<W: Write>(
   user_program_s: &str,
   err_stream: &mut W,
   interner: &mut Interner,
) -> Result<Program, CompilationError> {
   lex_and_parse(user_program_s, err_stream, interner)
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
