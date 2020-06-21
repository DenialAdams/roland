#[derive(Debug)]
pub enum Token {
   ProcedureDef,
   OpenBrace,
   CloseBrace,
   OpenParen,
   CloseParen,
   Semicolon,
   Identifier(String),
   StringLiteral(String),
}

enum LexMode {
   Normal,
   Ident,
   StringLiteral,
}

fn extract_keyword_or_ident(s: &str) -> Token {
   match s {
      "proc" => Token::ProcedureDef,
      other => Token::Identifier(other.to_string()),
   }
}

pub fn lex(input: String) -> Result<Vec<Token>, ()> {
   let mut tokens = Vec::new();
   let mut mode = LexMode::Normal;
   let mut str_buf = String::new();
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
            } else if c == ';' {
               tokens.push(Token::Semicolon);
               let _ = chars.next().unwrap();
            } else if c.is_alphabetic() {
               mode = LexMode::Ident;
            } else {
               eprintln!("Encountered unexpected character {}", c);
               return Err(());
            }
         }
         LexMode::Ident => {
            if !c.is_alphabetic() && !c.is_alphanumeric() {
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
      LexMode::StringLiteral => {
         eprintln!("Encountered EOF while parsing string literal; Are you missing a closing \"?");
         Err(())
      }
   }
}
