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
      eprintln!("got {:?} when expecting {:?}", lex_token, token);
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
   Equality,
   NotEquality,
   GreaterThan,
   LessThan,
   GreaterThanOrEqualTo,
   LessThanOrEqualTo,
}

pub enum Expression {
   ProcedureCall(String, Vec<Expression>),
   StringLiteral(String),
   IntLiteral(i64),
   Variable(String),
   BinaryOperator(BinOp, Box<(Expression, Expression)>),
   Negate(Box<Expression>),
}

pub enum Statement {
   ExpressionStatement(Expression),
   VariableDeclaration(String, Expression),
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
         Token::KeywordProcedureDef => {
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
   expect(l, discriminant(&Token::KeywordProcedureDef))?;
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
         Some(Token::KeywordLet) => {
            let _ = l.next();
            let variable_name = expect(l, discriminant(&Token::Identifier(String::from(""))))?;
            expect(l, discriminant(&Token::Assignment))?;
            let e = parse_expression(l)?;
            expect(l, discriminant(&Token::Semicolon))?;
            statements.push(Statement::VariableDeclaration(extract_identifier(variable_name), e));
         }
         Some(Token::Identifier(_))
         | Some(Token::StringLiteral(_))
         | Some(Token::IntLiteral(_))
         | Some(Token::OpenParen)
         | Some(Token::Minus) => {
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

fn parse_arguments(l: &mut Lexer) -> Result<Vec<Expression>, ()> {
   let mut arguments = vec![];

   loop {
      match l.peek() {
         Some(Token::Identifier(_))
         | Some(Token::StringLiteral(_))
         | Some(Token::IntLiteral(_))
         | Some(Token::OpenParen)
         | Some(Token::Minus) => {
            let e = parse_expression(l)?;
            arguments.push(e);
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::CloseParen)) {
               break;
            }
            expect(l, discriminant(&Token::Comma))?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         x => {
            eprintln!(
               "While parsing arguments - unexpected token {:?}; was expecting an expression or )",
               x
            );
            return Err(());
         }
      }
   }

   Ok(arguments)
}

fn parse_expression(l: &mut Lexer) -> Result<Expression, ()> {
   pratt(l, 0)
}

fn pratt(l: &mut Lexer, min_bp: u8) -> Result<Expression, ()> {
   let lhs = l.next();
   let lhs = match lhs {
      Some(Token::IntLiteral(x)) => Expression::IntLiteral(x),
      Some(Token::StringLiteral(x)) => Expression::StringLiteral(x),
      Some(Token::Identifier(s)) => {
         if let Some(&Token::OpenParen) = l.peek() {
            let _ = l.next();
            let args = parse_arguments(l)?;
            expect(l, discriminant(&Token::CloseParen))?;
            Expression::ProcedureCall(s, args)
         } else {
            Expression::Variable(s)
         }
      }
      Some(Token::OpenParen) => {
         let new_lhs = pratt(l, 0)?;
         expect(l, discriminant(&Token::CloseParen))?;
         new_lhs
      }
      Some(x @ Token::Minus) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, r_bp)?;
         Expression::Negate(Box::new(rhs))
      }
      x => {
         eprintln!(
            "While parsing expression - unexpected token {:?}; was expecting an int, identifier, or prefix operator",
            x
         );
         return Err(());
      }
   };

   loop {
      // TODO: use something like discriminant, or maybe better a new enum type so we avoid the clone
      let op: Token = match l.peek() {
         Some(x @ &Token::Plus)
         | Some(x @ &Token::Minus)
         | Some(x @ &Token::Multiply)
         | Some(x @ &Token::Divide)
         | Some(x @ &Token::LessThan)
         | Some(x @ &Token::LessThanOrEqualTo)
         | Some(x @ &Token::GreaterThan)
         | Some(x @ &Token::GreaterThanOrEqualTo)
         | Some(x @ &Token::Equality)
         | Some(x @ &Token::NotEquality) => x.clone(),
         _ => break,
      };

      let (l_bp, r_b) = infix_binding_power(&op);
      if l_bp < min_bp {
         break;
      }

      let _ = l.next();
      let rhs = pratt(l, r_b)?;

      let bin_op = match op {
         Token::Plus => BinOp::Add,
         Token::Minus => BinOp::Subtract,
         Token::Multiply => BinOp::Multiply,
         Token::Divide => BinOp::Divide,
         Token::GreaterThan => BinOp::GreaterThan,
         Token::GreaterThanOrEqualTo => BinOp::GreaterThanOrEqualTo,
         Token::LessThan => BinOp::LessThan,
         Token::LessThanOrEqualTo => BinOp::LessThanOrEqualTo,
         Token::Equality => BinOp::Equality,
         Token::NotEquality => BinOp::NotEquality,
         _ => unreachable!(),
      };

      return Ok(Expression::BinaryOperator(bin_op, Box::new((rhs, lhs))));
   }

   Ok(lhs)
}

fn prefix_binding_power(op: &Token) -> ((), u8) {
   match op {
      Token::Minus => ((), 6),
      _ => panic!("bad op: {:?}", op),
   }
}

fn infix_binding_power(op: &Token) -> (u8, u8) {
   match &op {
      Token::Equality
      | Token::NotEquality
      | Token::GreaterThan
      | Token::GreaterThanOrEqualTo
      | Token::LessThan
      | Token::LessThanOrEqualTo => (1, 1),
      Token::Plus | Token::Minus => (2, 3),
      Token::Multiply | Token::Divide => (4, 5),
      _ => unreachable!(),
   }
}
