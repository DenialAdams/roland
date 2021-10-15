use std::io::Write;

use crate::interner::{Interner, StrId};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SourceInfo {
   pub line: usize,
   pub col: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SourceToken {
   pub token: Token,
   pub source_info: SourceInfo,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
   Arrow,
   KeywordElse,
   KeywordFuncDef,
   KeywordIf,
   KeywordProcedureDef,
   KeywordStructDef,
   KeywordLet,
   KeywordReturn,
   KeywordLoop,
   KeywordContinue,
   KeywordBreak,
   KeywordExtend,
   KeywordTruncate,
   KeywordTransmute,
   KeywordStatic,
   OpenBrace,
   CloseBrace,
   OpenParen,
   CloseParen,
   OpenSquareBracket,
   CloseSquareBracket,
   Colon,
   Caret,
   Amp,
   Pipe,
   Semicolon,
   Identifier(StrId),
   BoolLiteral(bool),
   StringLiteral(StrId),
   IntLiteral(i64),
   FloatLiteral(f64),
   Plus,
   Minus,
   MultiplyDeref,
   Divide,
   Remainder,
   Assignment,
   Equality,
   NotEquality,
   LessThan,
   LessThanOrEqualTo,
   GreaterThan,
   GreaterThanOrEqualTo,
   Comma,
   Exclam,
   Period,
}

enum LexMode {
   Normal,
   Ident,
   StringLiteral,
   StringLiteralEscape,
   NumericLiteral,
}

pub fn emit_source_info<W: Write>(err_stream: &mut W, source_info: SourceInfo) {
   writeln!(err_stream, "↳ line {}, column {}", source_info.line, source_info.col).unwrap();
}

fn extract_keyword_or_ident(s: &str, interner: &mut Interner) -> Token {
   match s {
      "true" => Token::BoolLiteral(true),
      "false" => Token::BoolLiteral(false),
      "else" => Token::KeywordElse,
      "func" => Token::KeywordFuncDef,
      "if" => Token::KeywordIf,
      "proc" => Token::KeywordProcedureDef,
      "struct" => Token::KeywordStructDef,
      "let" => Token::KeywordLet,
      "return" => Token::KeywordReturn,
      "loop" => Token::KeywordLoop,
      "break" => Token::KeywordBreak,
      "continue" => Token::KeywordContinue,
      "extend" => Token::KeywordExtend,
      "truncate" => Token::KeywordTruncate,
      "transmute" => Token::KeywordTransmute,
      "static" => Token::KeywordStatic,
      other => Token::Identifier(interner.intern(other)),
   }
}

pub fn lex<W: Write>(input: &str, err_stream: &mut W, interner: &mut Interner) -> Result<Vec<SourceToken>, ()> {
   let mut tokens: Vec<SourceToken> = Vec::new();
   let mut mode = LexMode::Normal;

   let mut source_info = SourceInfo { line: 1, col: 1 };

   // Temporary buffer we use in various parts of the lexer
   let mut str_buf = String::new();

   // identifiers and string literal
   let mut str_begin = source_info;

   // numeric literals
   let mut is_float = false;

   let mut chars = input.chars().peekable();

   while let Some(c) = chars.peek().copied() {
      match mode {
         LexMode::Normal => {
            if c == '\n' {
               source_info.line += 1;
               source_info.col = 1;
               let _ = chars.next().unwrap();
            } else if c.is_whitespace() {
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '"' {
               mode = LexMode::StringLiteral;
               str_begin = source_info;
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '{' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::OpenBrace,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '}' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::CloseBrace,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '(' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::OpenParen,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ')' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::CloseParen,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ':' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Colon,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ';' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Semicolon,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '+' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Plus,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '-' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'>') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Arrow,
                  });
                  source_info.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Minus,
                  });
                  source_info.col += 1;
               }
            } else if c == '*' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::MultiplyDeref,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '/' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Divide,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '%' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Remainder,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ',' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Comma,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '&' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Amp,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '^' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Caret,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '|' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Pipe,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '=' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Equality,
                  });
                  source_info.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Assignment,
                  });
                  source_info.col += 1;
               }
            } else if c == '>' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::GreaterThanOrEqualTo,
                  });
                  source_info.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::GreaterThan,
                  });
                  source_info.col += 1;
               }
            } else if c == '<' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::LessThanOrEqualTo,
                  });
                  source_info.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::LessThan,
                  });
                  source_info.col += 1;
               }
            } else if c == '!' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::NotEquality,
                  });
                  source_info.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Exclam,
                  });
                  source_info.col += 1;
               }
            } else if c == '.' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Period,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '[' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::OpenSquareBracket,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ']' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::CloseSquareBracket,
               });
               source_info.col += 1;
               let _ = chars.next().unwrap();
            } else if c.is_ascii_digit() {
               mode = LexMode::NumericLiteral;
            } else if c.is_alphabetic() || c == '_' {
               mode = LexMode::Ident;
            } else {
               writeln!(err_stream, "Encountered unexpected character {}", c).unwrap();
               emit_source_info(err_stream, source_info);
               return Err(());
            }
         }
         LexMode::Ident => {
            if !c.is_alphanumeric() && c != '_' {
               let resulting_token = extract_keyword_or_ident(&str_buf, interner);
               tokens.push(SourceToken {
                  source_info,
                  token: resulting_token,
               });
               source_info.col += str_buf.len();
               str_buf.clear();
               mode = LexMode::Normal;
            } else {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            }
         }
         LexMode::StringLiteral => {
            if c == '"' {
               let final_str = interner.intern(&str_buf);
               tokens.push(SourceToken {
                  source_info: str_begin,
                  token: Token::StringLiteral(final_str),
               });
               str_buf.clear();
               mode = LexMode::Normal;
            } else if c == '\\' {
               mode = LexMode::StringLiteralEscape;
            } else {
               str_buf.push(c);
            }
            if c == '\n' {
               source_info.line += 1;
               source_info.col = 1;
            } else {
               source_info.col += 1;
            }
            let _ = chars.next().unwrap();
         }
         LexMode::StringLiteralEscape => {
            if c == '\\' {
               str_buf.push('\\');
            } else if c == 'n' {
               str_buf.push('\n');
            } else if c == 'r' {
               str_buf.push('\r');
            } else if c == 't' {
               str_buf.push('\t');
            } else if c == '0' {
               str_buf.push('\0');
            } else if c == '"' {
               str_buf.push('"');
            } else {
               writeln!(err_stream, "Encountered unknown escape sequence `\\{}`", c).unwrap();
               emit_source_info(
                  err_stream,
                  SourceInfo {
                     col: source_info.col - 1,
                     line: source_info.line,
                  },
               );
               return Err(());
            }
            source_info.col += 1;
            let _ = chars.next().unwrap();
            mode = LexMode::StringLiteral;
         }
         LexMode::NumericLiteral => {
            if c.is_ascii_digit() {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            } else if c == '.' && !is_float {
               is_float = true;
               str_buf.push(c);
               let _ = chars.next().unwrap();
            } else {
               tokens.push(finish_numeric_literal(&str_buf, err_stream, source_info, is_float)?);
               source_info.col += str_buf.len();
               is_float = false;
               str_buf.clear();
               mode = LexMode::Normal;
            }
         }
      }
   }

   match mode {
      LexMode::Normal => Ok(tokens),
      // Probably no valid program ends with a keyword or identifier, but we'll let the parser determine that
      LexMode::Ident => {
         let resulting_token = extract_keyword_or_ident(&str_buf, interner);
         tokens.push(SourceToken {
            source_info,
            token: resulting_token,
         });
         source_info.col += str_buf.len();
         Ok(tokens)
      }
      // Same for numbers
      LexMode::NumericLiteral => {
         tokens.push(finish_numeric_literal(&str_buf, err_stream, source_info, is_float)?);
         Ok(tokens)
      }
      LexMode::StringLiteral | LexMode::StringLiteralEscape => {
         writeln!(
            err_stream,
            "Encountered EOF while parsing string literal; Are you missing a closing \"?"
         )
         .unwrap();
         writeln!(
            err_stream,
            "↳ string literal @ line {}, column {}",
            str_begin.line, str_begin.col
         )
         .unwrap();
         writeln!(
            err_stream,
            "↳ EOF @ line {}, column {}",
            source_info.line, source_info.col
         )
         .unwrap();
         Err(())
      }
   }
}

fn finish_numeric_literal<W: Write>(
   s: &str,
   err_stream: &mut W,
   source_info: SourceInfo,
   is_float: bool,
) -> Result<SourceToken, ()> {
   let resulting_token = if is_float {
      let float_value = match fast_float::parse(s) {
         Ok(v) => v,
         Err(_) => {
            writeln!(err_stream, "Encountered number that can't be parsed as a float").unwrap();
            emit_source_info(err_stream, source_info);
            return Err(());
         }
      };
      Token::FloatLiteral(float_value)
   } else {
      let int_value = match parse_int(s) {
         Ok(v) => v,
         Err(_) => {
            writeln!(err_stream, "Encountered number that is TOO BIG!!").unwrap();
            emit_source_info(err_stream, source_info);
            return Err(());
         }
      };
      Token::IntLiteral(int_value)
   };
   Ok(SourceToken {
      source_info,
      token: resulting_token,
   })
}

// The string provided MUST be a valid number, or we'll assert
// An Err is returned if overflow would occur
fn parse_int(s: &str) -> Result<i64, ()> {
   let mut int_value: i64 = 0;

   for b in s.as_bytes() {
      let digit: i64 = match b {
         b'0' => 0,
         b'1' => 1,
         b'2' => 2,
         b'3' => 3,
         b'4' => 4,
         b'5' => 5,
         b'6' => 6,
         b'7' => 7,
         b'8' => 8,
         b'9' => 9,
         _ => unreachable!(),
      };

      let new_val = int_value.checked_mul(10).and_then(|x| x.checked_add(digit));

      int_value = if let Some(v) = new_val {
         v
      } else {
         return Err(());
      };
   }

   Ok(int_value)
}
