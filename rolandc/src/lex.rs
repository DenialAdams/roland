use std::io::Write;
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

pub fn lex<W: Write>(input: &str, err_stream: &mut W) -> Result<Vec<Token>, ()> {
   let mut tokens = Vec::new();
   let mut mode = LexMode::Normal;
   let mut str_buf = String::new();
   let mut int_value: i64 = 0;
   let mut chars = input.chars().peekable();
   while let Some(c) = chars.peek().copied() {
      match mode {
         LexMode::Normal => {
            if c.is_whitespace() {
               let _ = chars.next().unwrap();
            } else if c == '"' {
               mode = LexMode::StringLiteral;
               let _ = chars.next().unwrap();
            } else if c == '{' {
               tokens.push(Token::OpenBrace);
               let _ = chars.next().unwrap();
            } else if c == '}' {
               tokens.push(Token::CloseBrace);
               let _ = chars.next().unwrap();
            } else if c == '(' {
               tokens.push(Token::OpenParen);
               let _ = chars.next().unwrap();
            } else if c == ')' {
               tokens.push(Token::CloseParen);
               let _ = chars.next().unwrap();
            } else if c == ':' {
               tokens.push(Token::Colon);
               let _ = chars.next().unwrap();
            } else if c == ';' {
               tokens.push(Token::Semicolon);
               let _ = chars.next().unwrap();
            } else if c == '+' {
               tokens.push(Token::Plus);
               let _ = chars.next().unwrap();
            } else if c == '-' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'>') {
                  tokens.push(Token::Arrow);
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(Token::Minus);
               }
            } else if c == '*' {
               tokens.push(Token::MultiplyDeref);
               let _ = chars.next().unwrap();
            } else if c == '/' {
               tokens.push(Token::Divide);
               let _ = chars.next().unwrap();
            } else if c == ',' {
               tokens.push(Token::Comma);
               let _ = chars.next().unwrap();
            } else if c == '&' {
               tokens.push(Token::Amp);
               let _ = chars.next().unwrap();
            } else if c == '^' {
               tokens.push(Token::Caret);
               let _ = chars.next().unwrap();
            } else if c == '|' {
               tokens.push(Token::Pipe);
               let _ = chars.next().unwrap();
            } else if c == '=' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(Token::Equality);
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(Token::Assignment);
               }
            } else if c == '>' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(Token::GreaterThanOrEqualTo);
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(Token::GreaterThan);
               }
            } else if c == '<' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(Token::LessThanOrEqualTo);
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(Token::LessThan);
               }
            } else if c == '!' {
               let _ = chars.next().unwrap();
               if chars.peek() == Some(&'=') {
                  tokens.push(Token::NotEquality);
                  let _ = chars.next().unwrap();
               } else {
                  tokens.push(Token::Exclam);
               }
            } else if c == '.' {
               tokens.push(Token::Period);
               let _ = chars.next().unwrap();
            } else if c.is_ascii_digit() {
               mode = LexMode::IntLiteral;
            } else if c.is_alphabetic() {
               mode = LexMode::Ident;
            } else {
               writeln!(err_stream, "Encountered unexpected character {}", c).unwrap();
               return Err(());
            }
         }
         LexMode::Ident => {
            if !c.is_alphabetic() && !c.is_alphanumeric() && c != '_' {
               let resulting_token = extract_keyword_or_ident(&str_buf);
               tokens.push(resulting_token);
               str_buf.clear();
               mode = LexMode::Normal;
            } else {
               str_buf.push(c);
               let _ = chars.next().unwrap();
            }
         }
         LexMode::StringLiteral => {
            if c == '"' {
               tokens.push(Token::StringLiteral(str_buf.clone()));
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
               tokens.push(resulting_token);
               int_value = 0;
               mode = LexMode::Normal;
            } else {
               let new_val = int_value
                  .checked_mul(10)
                  .and_then(|x| x.checked_add(c.to_digit(10).unwrap() as i64));
               int_value = if let Some(v) = new_val {
                  v
               } else {
                  writeln!(err_stream, "Encountered number that is TOO BIG!!").unwrap();
                  return Err(());
               };
               let _ = chars.next().unwrap();
            }
         }
      }
   }

   match mode {
      LexMode::Normal => Ok(tokens),
      // Probably no valid program ends with a keyword or identifier, but we'll let the parser determine that
      LexMode::Ident => {
         let resulting_token = extract_keyword_or_ident(&str_buf);
         tokens.push(resulting_token);
         Ok(tokens)
      }
      // Same for numbers
      LexMode::IntLiteral => {
         let resulting_token = Token::IntLiteral(int_value);
         tokens.push(resulting_token);
         Ok(tokens)
      }
      LexMode::StringLiteral => {
         writeln!(
            err_stream,
            "Encountered EOF while parsing string literal; Are you missing a closing \"?"
         )
         .unwrap();
         Err(())
      }
   }
}
