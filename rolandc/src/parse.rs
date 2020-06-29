use super::lex::Token;
use std::mem::{discriminant, Discriminant};

struct Lexer {
   tokens: Vec<Token>,
}

impl Lexer {
   fn from_tokens(mut tokens: Vec<Token>) -> Lexer {
      tokens.reverse();
      Lexer { tokens }
   }

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

pub struct ProcedureNode {
   pub name: String,
   pub block: BlockNode,
}

#[derive(Debug)]
pub enum BinOp {
   Add,
   Subtract,
   Multiply,
   Divide,
}

pub enum Expression {
   ProcedureCall(String),
   Int(i64),
   Variable(String),
   BinaryOperator(BinOp, Box<(Expression, Expression)>),
   Negate(Box<Expression>),
}

pub enum Statement {
   ExpressionStatement(Expression),
}

pub struct BlockNode {
   pub statements: Vec<Statement>,
}

pub struct Program {
   pub procedures: Vec<ProcedureNode>,
}

pub fn astify(tokens: Vec<Token>) -> Result<Program, ()> {
   let mut lexer = Lexer::from_tokens(tokens);

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

   Ok(Program { procedures })
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
         Some(Token::Identifier(_)) | Some(Token::IntLiteral(_)) | Some(Token::OpenParen) => {
            let e = parse_expression(l)?;
            expect(l, discriminant(&Token::Semicolon))?;
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
            eprintln!("While parsing block - unexpected EOF; was expecting a statement or a }}");
            return Err(());
         }
      }
   }
   Ok(BlockNode { statements })
}

fn parse_expression(l: &mut Lexer) -> Result<Expression, ()> {
   pratt(l, 0)
}

fn pratt(l: &mut Lexer, min_bp: u8) -> Result<Expression, ()> {
   let lhs = l.next();
   let lhs = match lhs {
      Some(Token::IntLiteral(x)) => Expression::Int(x),
      Some(Token::Identifier(s)) => {
         if let Some(&Token::OpenParen) = l.peek() {
            let _ = l.next();
            // TODO arguments
            let _ = l.next(); // "hello, world!"
            expect(l, discriminant(&Token::CloseParen))?;
            Expression::ProcedureCall(s)
         } else {
            Expression::Variable(s)
         }
      }
      Some(Token::OpenParen) => {
         let new_lhs = pratt(l, 0)?;
         expect(l, discriminant(&Token::CloseParen))?;
         new_lhs
      }
      Some(x @ Token::Plus) | Some(x @ Token::Minus) | Some(x @ Token::Multiply) | Some(x @ Token::Divide) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, r_bp)?;
         Expression::Negate(Box::new(rhs))
      }
      x => {
         eprintln!(
            "While parsing expression - unexpected token {:?}; was expecting an int or identifier",
            x
         );
         return Err(());
      }
   };

   loop {
      // TODO: use something like discriminant, or maybe better a new enum type so we avoid the clone
      let op: Token = match l.peek() {
         Some(x @ &Token::Plus) | Some(x @ &Token::Minus) | Some(x @ &Token::Multiply) | Some(x @ &Token::Divide) => {
            x.clone()
         }
         _ => break,
      };

      let (l_bp, r_b) = infix_binding_power(&op);
      if l_bp < min_bp {
         break;
      }

      let _ = l.next();
      let rhs = pratt(l, r_b)?;

      match op {
         Token::Plus => return Ok(Expression::BinaryOperator(BinOp::Add, Box::new((lhs, rhs)))),
         Token::Minus => return Ok(Expression::BinaryOperator(BinOp::Subtract, Box::new((lhs, rhs)))),
         Token::Multiply => return Ok(Expression::BinaryOperator(BinOp::Multiply, Box::new((lhs, rhs)))),
         Token::Divide => return Ok(Expression::BinaryOperator(BinOp::Divide, Box::new((lhs, rhs)))),
         _ => unreachable!(),
      }
   }

   Ok(lhs)
}

fn prefix_binding_power(op: &Token) -> ((), u8) {
   match op {
      Token::Minus => ((), 5),
      _ => panic!("bad op: {:?}", op),
   }
}

fn infix_binding_power(op: &Token) -> (u8, u8) {
   match &op {
      Token::Plus | Token::Minus => (1, 2),
      Token::Multiply | Token::Divide => (3, 4),
      _ => unreachable!(),
   }
}
