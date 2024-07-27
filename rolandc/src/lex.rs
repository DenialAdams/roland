use std::num::IntErrorKind;

use unicode_ident::{is_xid_continue, is_xid_start};

use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId};
use crate::source_info::{SourceInfo, SourcePath, SourcePosition};

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Token {
   Arrow,
   KeywordDefer,
   KeywordElse,
   KeywordIf,
   KeywordProc,
   KeywordStructDef,
   KeywordUnionDef,
   KeywordEnumDef,
   KeywordLet,
   KeywordReturn,
   KeywordLoop,
   KeywordContinue,
   KeywordBreak,
   KeywordAs,
   KeywordTransmute,
   KeywordConst,
   KeywordStatic,
   KeywordNamed,
   KeywordAnd,
   KeywordOr,
   KeywordFor,
   KeywordWhile,
   KeywordIn,
   KeywordExtern,
   KeywordBuiltin,
   KeywordImport,
   KeywordWhere,
   KeywordIfx,
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
   IntLiteral(u64),
   FloatLiteral(f64),
   Plus,
   Minus,
   Multiply,
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
   Deref,
   Eof,
   TripleUnderscore,
}

impl Token {
   #[must_use]
   pub fn for_parse_err(&self) -> &'static str {
      match self {
         Token::Arrow => "token '->'",
         Token::KeywordDefer => "keyword 'defer'",
         Token::KeywordElse => "keyword 'else'",
         Token::KeywordIf => "keyword 'if'",
         Token::KeywordProc => "keyword 'proc'",
         Token::KeywordStructDef => "keyword 'struct'",
         Token::KeywordUnionDef => "keyword 'union'",
         Token::KeywordLet => "keyword 'let'",
         Token::KeywordReturn => "keyword 'return'",
         Token::KeywordLoop => "keyword 'loop'",
         Token::KeywordContinue => "keyword 'continue'",
         Token::KeywordBreak => "keyword 'break'",
         Token::KeywordAs => "keyword 'as'",
         Token::KeywordTransmute => "keyword 'transmute'",
         Token::KeywordConst => "keyword 'const'",
         Token::KeywordStatic => "keyword 'static'",
         Token::KeywordNamed => "keyword 'named'",
         Token::KeywordAnd => "keyword 'and'",
         Token::KeywordOr => "keyword 'or'",
         Token::KeywordEnumDef => "keyword 'enum'",
         Token::KeywordExtern => "keyword 'extern'",
         Token::KeywordBuiltin => "keyword 'builtin'",
         Token::KeywordImport => "keyword 'import'",
         Token::KeywordWhere => "keyword 'where'",
         Token::KeywordIfx => "keyword 'ifx'",
         Token::OpenBrace => "token '{'",
         Token::CloseBrace => "token '}'",
         Token::OpenParen => "token '('",
         Token::CloseParen => "token ')'",
         Token::OpenSquareBracket => "token '['",
         Token::CloseSquareBracket => "token ']'",
         Token::Colon => "token ':'",
         Token::DoubleColon => "token '::'",
         Token::Caret => "token '^'",
         Token::Amp => "token '&'",
         Token::Pipe => "token '|'",
         Token::Semicolon => "token ';'",
         Token::Identifier(_) => "identifier",
         Token::BoolLiteral(_) => "boolean literal",
         Token::StringLiteral(_) => "string literal",
         Token::IntLiteral(_) => "int literal",
         Token::FloatLiteral(_) => "float literal",
         Token::Plus => "token '+'",
         Token::Minus => "token '-'",
         Token::Multiply => "token '*'",
         Token::Divide => "token '/'",
         Token::Remainder => "token '%'",
         Token::Assignment => "token '='",
         Token::Equality => "token '=='",
         Token::NotEquality => "token '!='",
         Token::LessThan => "token '<'",
         Token::LessThanOrEqualTo => "token '<='",
         Token::GreaterThan => "token '>'",
         Token::GreaterThanOrEqualTo => "token '>='",
         Token::Comma => "token ','",
         Token::Exclam => "token '!'",
         Token::Period => "token '.'",
         Token::DoublePeriod => "token '..'",
         Token::ShiftLeft => "token '<<'",
         Token::ShiftRight => "token '>>'",
         Token::KeywordFor => "keyword 'for'",
         Token::KeywordWhile => "keyword 'while'",
         Token::KeywordIn => "keyword 'in'",
         Token::Dollar => "token '$'",
         Token::Deref => "token '~'",
         Token::TripleUnderscore => "token '___'",
         Token::Eof => "EOF",
      }
   }
}

enum LexMode {
   Normal,
   Ident,
   StringLiteral,
   StringLiteralEscape,
   NumericLiteral,
   FloatLiteralAfterE,
   Comment,
}

fn extract_keyword_or_ident(s: &str, interner: &mut Interner) -> Token {
   match s {
      "true" => Token::BoolLiteral(true),
      "false" => Token::BoolLiteral(false),
      "else" => Token::KeywordElse,
      "defer" => Token::KeywordDefer,
      "if" => Token::KeywordIf,
      "proc" => Token::KeywordProc,
      "struct" => Token::KeywordStructDef,
      "union" => Token::KeywordUnionDef,
      "let" => Token::KeywordLet,
      "return" => Token::KeywordReturn,
      "loop" => Token::KeywordLoop,
      "break" => Token::KeywordBreak,
      "continue" => Token::KeywordContinue,
      "as" => Token::KeywordAs,
      "transmute" => Token::KeywordTransmute,
      "const" => Token::KeywordConst,
      "static" => Token::KeywordStatic,
      "named" => Token::KeywordNamed,
      "and" => Token::KeywordAnd,
      "or" => Token::KeywordOr,
      "enum" => Token::KeywordEnumDef,
      "in" => Token::KeywordIn,
      "for" => Token::KeywordFor,
      "while" => Token::KeywordWhile,
      "extern" => Token::KeywordExtern,
      "builtin" => Token::KeywordBuiltin,
      "import" => Token::KeywordImport,
      "where" => Token::KeywordWhere,
      "ifx" => Token::KeywordIfx,
      other => Token::Identifier(interner.intern(other)),
   }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct SourceToken {
   pub token: Token,
   pub source_info: SourceInfo,
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
      std::mem::replace(&mut self.length_in_chars, 0)
   }
}

pub fn lex(
   input: &str,
   source_path: SourcePath,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
) -> Result<Lexer, ()> {
   lex_for_tokens(input, source_path, err_manager, interner).map(|x| Lexer::from_tokens(x, source_path))
}

pub fn lex_for_tokens(
   input: &str,
   source_path: SourcePath,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
) -> Result<Vec<SourceToken>, ()> {
   let mut tokens: Vec<SourceToken> = Vec::new();
   let mut mode = LexMode::Normal;

   let mut cur_position = SourcePosition { line: 0, col: 0 };

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
               cur_position.col = 0;
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
                     token: Token::Colon,
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
                  token: Token::Multiply,
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
            } else if c == '~' {
               tokens.push(SourceToken {
                  source_info: SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  token: Token::Deref,
               });
               cur_position.col += 1;
               let _ = chars.next().unwrap();
            } else if c.is_ascii_digit() {
               mode = LexMode::NumericLiteral;
            } else if is_xid_start(c) || c == '_' {
               mode = LexMode::Ident;
            } else {
               rolandc_error!(
                  err_manager,
                  SourceInfo {
                     begin: cur_position,
                     end: cur_position.next_col(),
                     file: source_path,
                  },
                  "Encountered unexpected character {}",
                  c,
               );
               return Err(());
            }
         }
         LexMode::Ident => {
            if is_xid_continue(c) {
               str_buf.push(c);
               let _ = chars.next().unwrap();
               if str_buf.buf == "__END__" {
                  // reset the lexing mode so we don't push __END__ as a token
                  mode = LexMode::Normal;
                  break;
               } else if str_buf.buf == "___" {
                  // Looking for this token in identifier lexing is pretty hacky,
                  // but we do it for n-lookahead (in this case, n=2.)
                  // It would be nice if we had arbitrary lookahead, perhaps by
                  // manually keeping track of the byte index.
                  tokens.push(SourceToken {
                     source_info: SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(str_buf.length_in_chars),
                        file: source_path,
                     },
                     token: Token::TripleUnderscore,
                  });
                  cur_position.col += str_buf.clear();
                  mode = LexMode::Normal;
               }
            } else {
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
               cur_position.col = 0;
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
               let escape_begin = SourcePosition {
                  col: cur_position.col - 1,
                  line: cur_position.line,
               };
               cur_position.col += 1;
               rolandc_error!(
                  err_manager,
                  SourceInfo {
                     begin: escape_begin,
                     end: cur_position,
                     file: source_path,
                  },
                  "Encountered unknown escape sequence `\\{}`",
                  c
               );
               return Err(());
            }
            let _ = chars.next().unwrap();
            mode = LexMode::StringLiteral;
         }
         LexMode::NumericLiteral => {
            // Alphanumeric because we support parsing hex, i.e. 0xff
            // '-' to support i.e. 3.14E-10
            if (c == 'e' || c == 'E') && !str_buf.buf.starts_with("0x") {
               str_buf.push(c);
               is_float = true;
               let _ = chars.next().unwrap();
               mode = LexMode::FloatLiteralAfterE;
            } else if c.is_ascii_alphanumeric() {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            } else if c == '_' {
               let _ = chars.next().unwrap();
            } else if c == '.' {
               let _ = chars.next().unwrap();
               if chars.peek().copied() == Some('.') {
                  // This is pretty hacky, but oh well
                  tokens.push(finish_numeric_literal(
                     &str_buf.buf,
                     err_manager,
                     SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(str_buf.length_in_chars),
                        file: source_path,
                     },
                     is_float,
                  )?);
                  cur_position.col += str_buf.clear();
                  is_float = false;
                  mode = LexMode::Normal;

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
               } else if !is_float {
                  is_float = true;
                  str_buf.push(c);
               } else {
                  tokens.push(finish_numeric_literal(
                     &str_buf.buf,
                     err_manager,
                     SourceInfo {
                        begin: cur_position,
                        end: cur_position.col_plus(str_buf.length_in_chars),
                        file: source_path,
                     },
                     is_float,
                  )?);
                  cur_position.col += str_buf.clear();
                  is_float = false;
                  mode = LexMode::Normal;
               }
            } else {
               tokens.push(finish_numeric_literal(
                  &str_buf.buf,
                  err_manager,
                  SourceInfo {
                     begin: cur_position,
                     end: cur_position.col_plus(str_buf.length_in_chars),
                     file: source_path,
                  },
                  is_float,
               )?);
               cur_position.col += str_buf.clear();
               is_float = false;
               mode = LexMode::Normal;
            }
         }
         LexMode::FloatLiteralAfterE => {
            if c.is_ascii_digit()
               || ((c == '-' || c == '+') && str_buf.buf.as_bytes().last().map(u8::to_ascii_lowercase) == Some(b'e'))
            {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            } else {
               tokens.push(finish_numeric_literal(
                  &str_buf.buf,
                  err_manager,
                  SourceInfo {
                     begin: cur_position,
                     end: cur_position.col_plus(str_buf.length_in_chars),
                     file: source_path,
                  },
                  is_float,
               )?);
               cur_position.col += str_buf.clear();
               is_float = false;
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
      LexMode::NumericLiteral | LexMode::FloatLiteralAfterE => {
         tokens.push(finish_numeric_literal(
            &str_buf.buf,
            err_manager,
            SourceInfo {
               begin: cur_position,
               end: cur_position.col_plus(str_buf.length_in_chars),
               file: source_path,
            },
            is_float,
         )?);
         cur_position.col += str_buf.clear();
         Ok(tokens)
      }
      LexMode::StringLiteral | LexMode::StringLiteralEscape => {
         let str_lit_loc = SourceInfo {
            begin: str_begin,
            end: cur_position,
            file: source_path,
         };
         rolandc_error!(
            err_manager,
            str_lit_loc,
            "Encountered EOF while parsing string literal. Hint: Are you missing a closing \"?"
         );
         Err(())
      }
   }
}

fn finish_numeric_literal(
   s: &str,
   err_manager: &mut ErrorManager,
   source_info: SourceInfo,
   is_float: bool,
) -> Result<SourceToken, ()> {
   let resulting_token = if is_float {
      let Ok(float_value) = s.parse::<f64>() else {
         rolandc_error!(
            err_manager,
            source_info,
            "Encountered number that can't be parsed as a float"
         );
         return Err(());
      };
      Token::FloatLiteral(float_value)
   } else if let Some(rest_of_s) = s.strip_prefix("0x") {
      parse_int(rest_of_s, 16, err_manager, source_info)?
   } else if let Some(rest_of_s) = s.strip_prefix("0o") {
      parse_int(rest_of_s, 8, err_manager, source_info)?
   } else if let Some(rest_of_s) = s.strip_prefix("0b") {
      parse_int(rest_of_s, 2, err_manager, source_info)?
   } else {
      parse_int(s, 10, err_manager, source_info)?
   };
   Ok(SourceToken {
      source_info,
      token: resulting_token,
   })
}

fn parse_int(s: &str, radix: u32, err_manager: &mut ErrorManager, source_info: SourceInfo) -> Result<Token, ()> {
   match u64::from_str_radix(s, radix) {
      Ok(v) => Ok(Token::IntLiteral(v)),
      Err(pe) if *pe.kind() == IntErrorKind::InvalidDigit => {
         rolandc_error!(
            err_manager,
            source_info,
            "Encountered invalid digit while parsing integer"
         );
         Err(())
      }
      Err(pe) if *pe.kind() == IntErrorKind::PosOverflow => {
         rolandc_error!(err_manager, source_info, "Encountered overly big integer");
         Err(())
      }
      Err(pe) if *pe.kind() == IntErrorKind::Empty => {
         rolandc_error!(
            err_manager,
            source_info,
            "Encountered empty integer literal (prefix that is not followed by a number)"
         );
         Err(())
      }
      Err(_) => unreachable!(),
   }
}

pub struct Lexer {
   tokens: Vec<SourceToken>,
   eof_location: SourceInfo,
   cur_position: usize,
}

impl Lexer {
   pub fn from_tokens(tokens: Vec<SourceToken>, file: SourcePath) -> Lexer {
      let eof_location = tokens.last().map_or(
         SourceInfo {
            begin: SourcePosition { line: 0, col: 0 },
            end: SourcePosition { line: 0, col: 0 },
            file,
         },
         |x| SourceInfo {
            begin: x.source_info.end,
            end: x.source_info.end,
            file: x.source_info.file,
         },
      );
      Lexer {
         tokens,
         eof_location,
         cur_position: 0,
      }
   }

   pub fn peek_source(&self) -> SourceInfo {
      self
         .tokens
         .get(self.cur_position)
         .map_or(self.eof_location, |x| x.source_info)
   }

   pub fn peek_token(&self) -> Token {
      self.tokens.get(self.cur_position).map_or(Token::Eof, |x| x.token)
   }

   pub fn double_peek_token(&self) -> Token {
      self.tokens.get(self.cur_position + 1).map_or(Token::Eof, |x| x.token)
   }

   pub fn peek_mut(&mut self) -> Option<&mut SourceToken> {
      self.tokens.get_mut(self.cur_position)
   }

   pub fn next(&mut self) -> SourceToken {
      if self.cur_position >= self.tokens.len() {
         SourceToken {
            token: Token::Eof,
            source_info: self.eof_location,
         }
      } else {
         self.cur_position += 1;
         self.tokens[self.cur_position - 1]
      }
   }
}
