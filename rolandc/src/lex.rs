use std::io::Write;
use std::num::IntErrorKind;

use crate::interner::{Interner, StrId};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SourcePosition {
   pub line: usize,
   pub col: usize,
}

impl SourcePosition {
   fn next_col(&self) -> SourcePosition {
      SourcePosition {
         line: self.line,
         col: self.col + 1,
      }
   }

   fn col_plus(&self, n: usize) -> SourcePosition {
      SourcePosition {
         line: self.line,
         col: self.col + n,
      }
   }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SourceInfo {
   pub begin: SourcePosition,
   pub end: SourcePosition,
   pub file: SourcePath,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct SourceToken {
   pub token: Token,
   pub source_info: SourceInfo,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Token {
   Arrow,
   KeywordElse,
   KeywordIf,
   KeywordProcedureDef,
   KeywordStructDef,
   KeywordEnumDef,
   KeywordLet,
   KeywordReturn,
   KeywordLoop,
   KeywordContinue,
   KeywordBreak,
   KeywordExtend,
   KeywordTruncate,
   KeywordTransmute,
   KeywordConst,
   KeywordStatic,
   KeywordNamed,
   KeywordAnd,
   KeywordOr,
   KeywordFor,
   KeywordIn,
   KeywordExtern,
   KeywordBuiltin,
   KeywordImport,
   OpenBrace,
   CloseBrace,
   OpenParen,
   CloseParen,
   OpenSquareBracket,
   CloseSquareBracket,
   DoubleColon,
   Colon,
   Caret,
   Amp,
   Pipe,
   Semicolon,
   Identifier(StrId),
   BoolLiteral(bool),
   StringLiteral(StrId),
   IntLiteral(i128),
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
   ShiftLeft,
   ShiftRight,
   Comma,
   Exclam,
   Period,
   DoublePeriod,
   Dollar,
}

impl Token {
   pub fn for_parse_err(&self) -> &'static str {
      match self {
         Token::Arrow => "->",
         Token::KeywordElse => "keyword else",
         Token::KeywordIf => "keyword if",
         Token::KeywordProcedureDef => "keyword proc",
         Token::KeywordStructDef => "keyword struct",
         Token::KeywordLet => "keyword let",
         Token::KeywordReturn => "keyword return",
         Token::KeywordLoop => "keyword loop",
         Token::KeywordContinue => "keyword continue",
         Token::KeywordBreak => "keyword break",
         Token::KeywordExtend => "keyword extend",
         Token::KeywordTruncate => "keyword truncate",
         Token::KeywordTransmute => "keyword transmute",
         Token::KeywordConst => "keyword const",
         Token::KeywordStatic => "keyword static",
         Token::KeywordNamed => "keyword named",
         Token::KeywordAnd => "keyword and",
         Token::KeywordOr => "keyword or",
         Token::KeywordEnumDef => "keyword enum",
         Token::KeywordExtern => "keyword extern",
         Token::KeywordBuiltin => "keyword builtin",
         Token::KeywordImport => "keyword import",
         Token::OpenBrace => "{",
         Token::CloseBrace => "}",
         Token::OpenParen => "(",
         Token::CloseParen => ")",
         Token::OpenSquareBracket => "[",
         Token::CloseSquareBracket => "]",
         Token::Colon => ":",
         Token::DoubleColon => "::",
         Token::Caret => "^",
         Token::Amp => "&",
         Token::Pipe => "|",
         Token::Semicolon => ";",
         Token::Identifier(_) => "identifier",
         Token::BoolLiteral(_) => "boolean literal",
         Token::StringLiteral(_) => "string literal",
         Token::IntLiteral(_) => "int literal",
         Token::FloatLiteral(_) => "float literal",
         Token::Plus => "+",
         Token::Minus => "-",
         Token::MultiplyDeref => "*",
         Token::Divide => "/",
         Token::Remainder => "%",
         Token::Assignment => "=",
         Token::Equality => "==",
         Token::NotEquality => "!=",
         Token::LessThan => "<",
         Token::LessThanOrEqualTo => "<=",
         Token::GreaterThan => ">",
         Token::GreaterThanOrEqualTo => ">=",
         Token::Comma => ",",
         Token::Exclam => "!",
         Token::Period => ".",
         Token::DoublePeriod => ".",
         Token::ShiftLeft => "<<",
         Token::ShiftRight => ">>",
         Token::KeywordFor => "keyword for",
         Token::KeywordIn => "keyword in",
         Token::Dollar => "$",
      }
   }
}

enum LexMode {
   Normal,
   Ident,
   StringLiteral,
   StringLiteralEscape,
   NumericLiteral,
   Comment,
}

pub fn emit_source_info<W: Write>(err_stream: &mut W, source_info: SourceInfo, interner: &Interner) {
   match source_info.file {
      SourcePath::File(x) => {
         let path_str = interner.lookup(x);
         writeln!(
            err_stream,
            "↳ line {}, column {} [{}]",
            source_info.begin.line, source_info.begin.col, path_str
         )
         .unwrap();
      }
      SourcePath::Sandbox | SourcePath::Std => {
         writeln!(err_stream, "↳ line {}, column {}", source_info.begin.line, source_info.begin.col).unwrap();
      }
   }
}

pub fn emit_source_info_with_description<W: Write>(
   err_stream: &mut W,
   source_info: SourceInfo,
   description: &str,
   interner: &Interner,
) {
   match source_info.file {
      SourcePath::File(x) => {
         let path_str = interner.lookup(x);
         writeln!(
            err_stream,
            "↳ {} @ line {}, column {} [{}]",
            description, source_info.begin.line, source_info.begin.col, path_str
         )
         .unwrap();
      }
      SourcePath::Sandbox | SourcePath::Std => {
         writeln!(err_stream, "↳ {} @ line {}, column {}", description, source_info.begin.line, source_info.begin.col).unwrap();
      }
   }
}

fn extract_keyword_or_ident(s: &str, interner: &mut Interner) -> Token {
   match s {
      "true" => Token::BoolLiteral(true),
      "false" => Token::BoolLiteral(false),
      "else" => Token::KeywordElse,
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
      "const" => Token::KeywordConst,
      "static" => Token::KeywordStatic,
      "named" => Token::KeywordNamed,
      "and" => Token::KeywordAnd,
      "or" => Token::KeywordOr,
      "enum" => Token::KeywordEnumDef,
      "in" => Token::KeywordIn,
      "for" => Token::KeywordFor,
      "extern" => Token::KeywordExtern,
      "builtin" => Token::KeywordBuiltin,
      "import" => Token::KeywordImport,
      other => Token::Identifier(interner.intern(other)),
   }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SourcePath {
   Sandbox,
   Std,
   File(StrId),
}

struct CharCountingBuffer {
   length_in_chars: usize,
   buf: String,
}

impl CharCountingBuffer {
   fn push(&mut self, c: char) {
      self.buf.push(c);
      self.length_in_chars += 1;
   }

   fn clear(&mut self) -> usize {
      self.buf.clear();
      let len_before_reset = self.length_in_chars;
      self.length_in_chars = 0;
      len_before_reset
   }
}

pub fn lex<W: Write>(
   input: &str,
   source_path: SourcePath,
   err_stream: &mut W,
   interner: &mut Interner,
) -> Result<Vec<SourceToken>, ()> {
   let mut tokens: Vec<SourceToken> = Vec::new();
   let mut mode = LexMode::Normal;

   let mut cur_position = SourcePosition {
      line: 1,
      col: 1,
   };

   // Temporary buffer we use in various parts of the lexer
   let mut str_buf = CharCountingBuffer {
      length_in_chars: 0,
      buf: String::new(),
   };

   // identifiers and string literal
   let mut str_begin = cur_position;

   // numeric literals
   let mut is_float = false;

   let mut chars = input.chars().peekable();

   while let Some(c) = chars.peek().copied() {
      match mode {
         LexMode::Normal => {
            if c == '\n' {
               cur_position.line += 1;
               cur_position.col = 1;
               let _ = chars.next().unwrap();
            } else if c.is_whitespace() {
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '"' {
               mode = LexMode::StringLiteral;
               str_begin = cur_position;
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '{' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::OpenBrace,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '}' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::CloseBrace,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '(' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::OpenParen,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ')' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::CloseParen,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ':' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&':') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::DoubleColon,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Colon
                  });
                  cur_position.col += 1;
               }
            } else if c == ';' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Semicolon,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '+' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Plus,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '-' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'>') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::Arrow,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.next_col(),
                        file: source_path,
                     },
                     token: Token::Minus,
                  });
                  cur_position.col += 1;
               }
            } else if c == '*' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::MultiplyDeref,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '/' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'/') {
                  let _ = chars.next().unwrap();
                  mode = LexMode::Comment;
                  cur_position.col += 2;
               } else {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.next_col(),
                        file: source_path,
                     },
                     token: Token::Divide,
                  });
                  cur_position.col += 1;
               }
            } else if c == '%' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Remainder,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '$' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Dollar,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ',' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Comma,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '&' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Amp,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '^' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Caret,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '|' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Pipe,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == '=' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::Equality,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.next_col(),
                        file: source_path,
                     },
                     token: Token::Assignment,
                  });
                  cur_position.col += 1;
               }
            } else if c == '>' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::GreaterThanOrEqualTo,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else if chars.peek() == Some(&'>') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::ShiftRight,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.next_col(),
                        file: source_path,
                     },
                     token: Token::GreaterThan,
                  });
                  cur_position.col += 1;
               }
            } else if c == '<' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::LessThanOrEqualTo,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else if chars.peek() == Some(&'<') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::ShiftLeft,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.next_col(),
                        file: source_path,
                     },
                     token: Token::LessThan,
                  });
                  cur_position.col += 1;
               }
            } else if c == '!' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::NotEquality,
                  });
                  cur_position.col += 2;
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.next_col(),
                        file: source_path,
                     },
                     token: Token::Exclam,
                  });
                  cur_position.col += 1;
               }
            } else if c == '.' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'.') {
                  let _ = chars.next().unwrap();
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(2),
                        file: source_path,
                     },
                     token: Token::DoublePeriod,
                  });
                  cur_position.col += 2;
               } else {
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.next_col(),
                        file: source_path,
                     },
                     token: Token::Period,
                  });
                  cur_position.col += 1;
               }
            } else if c == '[' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::OpenSquareBracket,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c == ']' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::CloseSquareBracket,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c.is_ascii_digit() {
               mode = LexMode::NumericLiteral;
            } else if c.is_alphabetic() || c == '_' {
               mode = LexMode::Ident;
            } else {
               writeln!(err_stream, "Encountered unexpected character {}", c).unwrap();
               emit_source_info(err_stream, SourceInfo {
                  begin: cur_position,
                  end: cur_position.next_col(),
                  file: source_path,
               }, interner);
               return Err(());
            }
         }
         LexMode::Ident => {
            if !c.is_alphanumeric() && c != '_' {
               let resulting_token = extract_keyword_or_ident(&str_buf.buf, interner);
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.col_plus(str_buf.length_in_chars),
                     file: source_path,
                  },
                  token: resulting_token,
               });
               cur_position.col += str_buf.clear();
               mode = LexMode::Normal;
            } else {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            }
         }
         LexMode::StringLiteral => {
            if c == '"' {
               let final_str = interner.intern(&str_buf.buf);
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: str_begin,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
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
               cur_position.line += 1;
               cur_position.col = 1;
            } else {
               cur_position.col += 1;
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
               let escape_begin = SourcePosition {
                  col: cur_position.col - 1,
                  line: cur_position.line,
               };
               cur_position.col += 1;
               emit_source_info(
                  err_stream,
                  SourceInfo {
                     begin: escape_begin,
                     end: cur_position,
                     file: source_path,
                  },
                  interner,
               );
               return Err(());
            }
            let _ = chars.next().unwrap();
            mode = LexMode::StringLiteral;
         }
         LexMode::NumericLiteral => {
            // Alphanumeric because we support parsing hex, i.e. 0xff
            if c.is_ascii_alphanumeric() {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            } else if c == '_' {
               let _ = chars.next().unwrap();
            } else if c == '.' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'.') {
                  // This is pretty hacky, but oh well
                  tokens.push(finish_numeric_literal(
                     &str_buf.buf,
                     err_stream,
                     SourceInfo { begin: cur_position, end: cur_position.col_plus(str_buf.length_in_chars), file: source_path },
                     is_float,
                     interner,
                  )?);
                  cur_position.col += str_buf.clear();
                  is_float = false;
                  str_buf.clear();
                  mode = LexMode::Normal;

                  let _ = chars.next().unwrap();
                  tokens.push(SourceToken {
                     source_info: SourceInfo { begin: cur_position, end: cur_position.col_plus(2), file: source_path },
                     token: Token::DoublePeriod,
                  });
                  cur_position.col += 2;
               } else {
                  is_float = true;
                  str_buf.push(c);
               }
            } else {
               tokens.push(finish_numeric_literal(
                  &str_buf.buf,
                  err_stream,
                  SourceInfo { begin: cur_position, end: cur_position.col_plus(str_buf.length_in_chars), file: source_path },
                  is_float,
                  interner,
               )?);
               cur_position.col += str_buf.clear();
               is_float = false;
               str_buf.clear();
               mode = LexMode::Normal;
            }
         }
         LexMode::Comment => {
            if c == '\n' {
               cur_position.col = 0;
               cur_position.line += 1;
               mode = LexMode::Normal;
            } else {
               cur_position.col += 1;
            }
            let _ = chars.next().unwrap();
         }
      }
   }

   match mode {
      LexMode::Normal | LexMode::Comment => Ok(tokens),
      // Probably no valid program ends with a keyword or identifier, but we'll let the parser determine that
      LexMode::Ident => {
         let resulting_token = extract_keyword_or_ident(&str_buf.buf, interner);
         tokens.push(SourceToken {
            source_info: SourceInfo {
               begin: cur_position,
               end: cur_position.col_plus(str_buf.length_in_chars),
               file: source_path,
            },
            token: resulting_token,
         });
         cur_position.col += str_buf.clear();
         Ok(tokens)
      }
      // Same for numbers
      LexMode::NumericLiteral => {
         tokens.push(finish_numeric_literal(
            &str_buf.buf,
            err_stream,
            SourceInfo { begin: cur_position, end: cur_position.col_plus(str_buf.length_in_chars), file: source_path },
            is_float,
            interner,
         )?);
         cur_position.col += str_buf.clear();
         Ok(tokens)
      }
      LexMode::StringLiteral | LexMode::StringLiteralEscape => {
         writeln!(
            err_stream,
            "Encountered EOF while parsing string literal. Hint: Are you missing a closing \"?"
         )
         .unwrap();
         emit_source_info_with_description(err_stream, SourceInfo { begin: str_begin, end: cur_position, file: source_path }, "string literal", interner);
         emit_source_info_with_description(err_stream, SourceInfo { begin: cur_position, end: cur_position, file: source_path }, "EOF", interner);
         Err(())
      }
   }
}

fn finish_numeric_literal<W: Write>(
   s: &str,
   err_stream: &mut W,
   source_info: SourceInfo,
   is_float: bool,
   interner: &Interner,
) -> Result<SourceToken, ()> {
   let resulting_token = if is_float {
      let float_value = match s.parse::<f64>() {
         Ok(v) => v,
         Err(_) => {
            writeln!(err_stream, "Encountered number that can't be parsed as a float").unwrap();
            emit_source_info(err_stream, source_info, interner);
            return Err(());
         }
      };
      Token::FloatLiteral(float_value)
   } else if let Some(rest_of_s) = s.strip_prefix("0x") {
      parse_int(rest_of_s, 16, err_stream, source_info, interner)?
   } else if let Some(rest_of_s) = s.strip_prefix("0o") {
      parse_int(rest_of_s, 8, err_stream, source_info, interner)?
   } else if let Some(rest_of_s) = s.strip_prefix("0b") {
      parse_int(rest_of_s, 2, err_stream, source_info, interner)?
   } else {
      parse_int(s, 10, err_stream, source_info, interner)?
   };
   Ok(SourceToken {
      source_info,
      token: resulting_token,
   })
}

fn parse_int<W: Write>(
   s: &str,
   radix: u32,
   err_stream: &mut W,
   source_info: SourceInfo,
   interner: &Interner,
) -> Result<Token, ()> {
   match i128::from_str_radix(s, radix) {
      Ok(v) => Ok(Token::IntLiteral(v)),
      Err(pe) if *pe.kind() == IntErrorKind::InvalidDigit => {
         writeln!(err_stream, "Encountered invalid digit while parsing integer").unwrap();
         emit_source_info(err_stream, source_info, interner);
         Err(())
      }
      Err(pe) if *pe.kind() == IntErrorKind::PosOverflow => {
         writeln!(err_stream, "Encountered overly big integer").unwrap();
         emit_source_info(err_stream, source_info, interner);
         Err(())
      }
      Err(pe) if *pe.kind() == IntErrorKind::Empty => {
         writeln!(
            err_stream,
            "Encountered empty integer literal (prefix that is not followed by a number)"
         )
         .unwrap();
         emit_source_info(err_stream, source_info, interner);
         Err(())
      }
      Err(_) => unreachable!(),
   }
}
