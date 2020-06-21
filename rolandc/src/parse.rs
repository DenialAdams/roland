use super::lex::Token;
use std::mem::{discriminant, Discriminant};

struct Lexer {
   tokens: Vec<Token>,
}

impl Lexer {
   fn peek(&self) -> Option<&Token> {
      self.tokens.last()
   }

   fn next(&mut self) -> Option<Token> {
      self.tokens.pop()
   }
}

fn expect(l: &mut Lexer, token: Discriminant<Token>) -> Result<Token, ()> {
   let lex_token = l.next();
   if lex_token.as_ref().map(|x| discriminant(x) != token).unwrap_or(true) {
      return Err(());
   }
   Ok(lex_token.unwrap())
}

struct ProcedureNode {
   name: String,
   block: BlockNode,
}

enum Expression {
   ProcedureCall(String),
}

enum Statement {
   ExpressionStatement(Expression),
}

struct BlockNode {
   statements: Vec<StatementNode>,
}

pub struct Program {
   procedures: Vec<ProcedureNode>,
}

pub fn astify(mut tokens: Vec<Token>) -> Result<Program, ()> {
   tokens.reverse();
   let mut lexer = Lexer { tokens };

   let mut procedures = vec![];

   while let Some(peeked_token) = lexer.peek() {
      match peeked_token {
         Token::ProcedureDef => {
            match parse_procedure(&mut lexer) {
               Ok(p) => procedures.push(p),
               Err(()) => return Err(()),
            };
         }
         x => {
            eprintln!(
               "While parsing top level - unexpected token {:?}; was expecting a procedure or struct declaration",
               x
            );
            return Err(());
         }
      }
   }

   Ok(Program { procedures: vec![] })
}

fn extract_identifier(t: Token) -> String {
   match t {
      Token::Identifier(v) => v,
      _ => unreachable!(),
   }
}

fn parse_procedure(l: &mut Lexer) -> Result<ProcedureNode, ()> {
   expect(l, discriminant(&Token::ProcedureDef))?;
   let function_name = expect(l, discriminant(&Token::Identifier(String::from(""))))?;
   expect(l, discriminant(&Token::OpenParen))?;
   expect(l, discriminant(&Token::CloseParen))?;
   let block = parse_block(l)?;
   Ok(ProcedureNode {
      name: extract_identifier(function_name),
      block,
   })
}

fn parse_block(l: &mut Lexer) -> Result<BlockNode, ()> {
   expect(l, discriminant(&Token::OpenBrace))?;

   let mut statements = vec![];

   loop {
      match l.peek() {
         Some(Token::CloseBrace) => {
            let _ = l.next();
            break;
         }
         Some(Token::Identifier(x)) => {
            let e = parse_expression(l);
            statements.push(Statement::ExpressionStatement(e));
         }
         Some(x) => {
            eprintln!(
               "While parsing block - unexpected token {:?}; was expecting a statement",
               x
            );
            return Err(());
         }
         None => {
            eprintln!(
               "While parsing block - unexpected EOF; was expecting a statement or a }",
               x
            );
            return Err(());
         }
      }
   }
   Ok(BlockNode { statements: vec![] })
}

fn parse_expression(l: &mut Lexer) -> Result<Expression, ()> {

}
