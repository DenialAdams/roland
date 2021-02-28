use std::io::Write;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SourceInfo {
   line: usize,
   col: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SourceToken {
   pub token: Token,
   pub source_info: SourceInfo
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
   OpenBrace,
   CloseBrace,
   OpenParen,
   CloseParen,
   Colon,
   Caret,
   Amp,
   Pipe,
   Semicolon,
   Identifier(String),
   BoolLiteral(bool),
   StringLiteral(String),
   IntLiteral(i64),
   Plus,
   Minus,
   MultiplyDeref,
   Divide,
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
   IntLiteral,
}

pub fn emit_source_info<W: Write>(err_stream: &mut W, source_info: SourceInfo) {
   writeln!(err_stream, "↳ line {}, column {}", source_info.line, source_info.col).unwrap();
}

fn extract_keyword_or_ident(s: &str) -> Token {
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
      other => Token::Identifier(other.to_string()),
   }
}

pub fn lex<W: Write>(input: &str, err_stream: &mut W) -> Result<Vec<SourceToken>, ()> {
   let mut tokens: Vec<SourceToken> = Vec::new();
   let mut mode = LexMode::Normal;
   let mut str_buf = String::new();
   let mut int_value: i64 = 0;
   let mut int_length: usize = 0;
   let mut chars = input.chars().peekable();

   let mut source_info = SourceInfo {
      line: 1,
      col: 1,
   };

   while let Some(c) = chars.peek().copied() {
      match mode {
         LexMode::Normal => {
            if c.is_whitespace() {
               let _ = chars.next().unwrap();
            } else if c == '"' {
               mode = LexMode::StringLiteral;
               let _ = chars.next().unwrap();
            } else if c == '{' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::OpenBrace,
               });
               let _ = chars.next().unwrap();
            } else if c == '}' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::CloseBrace,
               });
               let _ = chars.next().unwrap();
            } else if c == '(' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::OpenParen,
               });
               let _ = chars.next().unwrap();
            } else if c == ')' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::CloseParen,
               });
               let _ = chars.next().unwrap();
            } else if c == ':' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Colon,
               });
               let _ = chars.next().unwrap();
            } else if c == ';' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Semicolon,
               });
               let _ = chars.next().unwrap();
            } else if c == '+' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Plus,
               });
               let _ = chars.next().unwrap();
            } else if c == '-' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'>') {
                  tokens.push(SourceToken {
                  source_info,
                  token: Token::Arrow,
               });
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                  source_info,
                  token: Token::Minus,
               });
               }
            } else if c == '*' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::MultiplyDeref,
               });
               let _ = chars.next().unwrap();
            } else if c == '/' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Divide,
               });
               let _ = chars.next().unwrap();
            } else if c == ',' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Comma,
               });
               let _ = chars.next().unwrap();
            } else if c == '&' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Amp,
               });
               let _ = chars.next().unwrap();
            } else if c == '^' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Caret,
               });
               let _ = chars.next().unwrap();
            } else if c == '|' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Pipe,
               });
               let _ = chars.next().unwrap();
            } else if c == '=' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Equality,
                  });
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Assignment,
                  });
               }
            } else if c == '>' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::GreaterThanOrEqualTo,
                  });
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::GreaterThan,
                  });
               }
            } else if c == '<' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::LessThanOrEqualTo,
                  });
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::LessThan,
                  });
               }
            } else if c == '!' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::NotEquality,
                  });
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info,
                     token: Token::Exclam,
                  });
               }
            } else if c == '.' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::Period,
               });
               let _ = chars.next().unwrap();
            } else if c.is_ascii_digit() {
               mode = LexMode::IntLiteral;
            } else if c.is_alphabetic() || c == '_' {
               mode = LexMode::Ident;
            } else {
               writeln!(err_stream, "Encountered unexpected character {}", c).unwrap();
               emit_source_info(err_stream, source_info);
               return Err(());
            }

            if c == '\n' {
               source_info.line += 1;
               source_info.col = 1;
            } else {
               source_info.col += 1;
            }
         }
         LexMode::Ident => {
            if !c.is_alphabetic() && !c.is_alphanumeric() && c != '_' {
               source_info.col += str_buf.len();
               let resulting_token = extract_keyword_or_ident(&str_buf);
               tokens.push(SourceToken {
                  source_info,
                  token: resulting_token,
               });
               str_buf.clear();
               mode = LexMode::Normal;
            } else {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            }
         }
         LexMode::StringLiteral => {
            if c == '"' {
               tokens.push(SourceToken {
                  source_info,
                  token: Token::StringLiteral(str_buf.clone()),
               });
               source_info.col += str_buf.len();
               source_info.col += 1; // closing quote
               str_buf.clear();
               mode = LexMode::Normal;
            } else {
               str_buf.push(c);
            }
            let _ = chars.next().unwrap();
         }
         LexMode::IntLiteral => {
            if !c.is_ascii_digit() {
               let resulting_token = Token::IntLiteral(int_value);
               tokens.push(SourceToken {
                  source_info,
                  token: resulting_token,
               });
               source_info.col += int_length;
               int_value = 0;
               int_length = 0;
               mode = LexMode::Normal;
            } else {
               let new_val = int_value
                  .checked_mul(10)
                  .and_then(|x| x.checked_add(c.to_digit(10).unwrap() as i64));
               int_value = if let Some(v) = new_val {
                  v
               } else {
                  writeln!(err_stream, "Encountered number that is TOO BIG!!").unwrap();
                  emit_source_info(err_stream, source_info);
                  return Err(());
               };

               int_length += 1;

               let _ = chars.next().unwrap();
            }
         }
      }
   }

   match mode {
      LexMode::Normal => Ok(tokens),
      // Probably no valid program ends with a keyword or identifier, but we'll let the parser determine that
      LexMode::Ident => {
         source_info.col += str_buf.len();
         let resulting_token = extract_keyword_or_ident(&str_buf);
         tokens.push(SourceToken {
            source_info,
            token: resulting_token,
         });
         Ok(tokens)
      }
      // Same for numbers
      LexMode::IntLiteral => {
         let resulting_token = Token::IntLiteral(int_value);
         tokens.push(SourceToken {
            source_info,
            token: resulting_token,
         });
         source_info.col += int_length;
         Ok(tokens)
      }
      LexMode::StringLiteral => {
         writeln!(
            err_stream,
            "Encountered EOF while parsing string literal; Are you missing a closing \"?"
         )
         .unwrap();
         emit_source_info(err_stream, source_info);
         Err(())
      }
   }
}
