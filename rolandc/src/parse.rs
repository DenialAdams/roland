use super::lex::Token;
use crate::type_data::{ExpressionType, ValueType};
use std::collections::{HashMap, HashSet};
use std::mem::discriminant;

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

   fn double_peek(&self) -> Option<&Token> {
      if self.tokens.len() <= 1 {
         return None;
      }

      self.tokens.get(self.tokens.len() - 2)
   }

   fn next(&mut self) -> Option<Token> {
      self.tokens.pop()
   }
}

fn expect(l: &mut Lexer, token: &Token) -> Result<Token, ()> {
   let lex_token = l.next();
   if lex_token
      .as_ref()
      .map(|x| discriminant(x) != discriminant(token))
      .unwrap_or(true)
   {
      eprintln!("got {:?} when expecting {:?}", lex_token, token);
      return Err(());
   }
   Ok(lex_token.unwrap())
}

pub struct ProcedureNode {
   pub name: String,
   pub parameters: Vec<(String, ExpressionType)>,
   pub locals: HashMap<String, ExpressionType>,
   pub block: BlockNode,
   pub ret_type: ExpressionType,
   pub pure: bool,
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
   BitwiseAnd,
   BitwiseOr,
   BitwiseXor,
}

#[derive(Debug, PartialEq)]
pub enum UnOp {
   Negate,
   Complement,
   AddressOf,
   Dereference,
}

#[derive(Debug)]

pub struct ExpressionNode {
   pub expression: Expression,
   pub exp_type: Option<ExpressionType>,
}

#[derive(Debug)]
pub enum Expression {
   ProcedureCall(String, Vec<ExpressionNode>),
   BoolLiteral(bool),
   StringLiteral(String),
   IntLiteral(i64),
   Variable(String),
   BinaryOperator(BinOp, Box<(ExpressionNode, ExpressionNode)>),
   UnaryOperator(UnOp, Box<ExpressionNode>),
}

impl Expression {
   pub fn is_lvalue(&self) -> bool {
      match self {
         Expression::Variable(_) => true,
         Expression::UnaryOperator(UnOp::Dereference, _) => true,
         _ => false,
      }
   }
}

pub enum Statement {
   AssignmentStatement(ExpressionNode, ExpressionNode),
   BlockStatement(BlockNode),
   ExpressionStatement(ExpressionNode),
   IfElseStatement(ExpressionNode, BlockNode, Box<Statement>),
   ReturnStatement(ExpressionNode),
   VariableDeclaration(String, ExpressionNode, Option<ExpressionType>),
}

pub struct BlockNode {
   pub statements: Vec<Statement>,
}

pub struct Program {
   pub procedures: Vec<ProcedureNode>,
   pub literals: HashSet<String>,
}

pub fn astify(tokens: Vec<Token>) -> Result<Program, ()> {
   let mut lexer = Lexer::from_tokens(tokens);

   let mut procedures = vec![];

   while let Some(peeked_token) = lexer.peek() {
      match peeked_token {
         Token::KeywordFuncDef => {
            let _ = lexer.next();
            let mut p = parse_procedure(&mut lexer)?;
            p.pure = true;
            procedures.push(p);
         }
         Token::KeywordProcedureDef => {
            let _ = lexer.next();
            let p = parse_procedure(&mut lexer)?;
            procedures.push(p);
         }
         x => {
            eprintln!(
               "While parsing top level - unexpected token {:?}; was expecting a function, procedure, or struct declaration",
               x
            );
            return Err(());
         }
      }
   }

   Ok(Program {
      procedures,
      literals: HashSet::new(),
   })
}

fn extract_identifier(t: Token) -> String {
   match t {
      Token::Identifier(v) => v,
      _ => unreachable!(),
   }
}

fn parse_procedure(l: &mut Lexer) -> Result<ProcedureNode, ()> {
   let function_name = expect(l, &Token::Identifier(String::from("")))?;
   expect(l, &Token::OpenParen)?;
   let parameters = parse_parameters(l)?;
   expect(l, &Token::CloseParen)?;
   let ret_type = if let Some(&Token::Arrow) = l.peek() {
      let _ = l.next();
      parse_type(l)?
   } else {
      ExpressionType::Value(ValueType::Unit)
   };
   let block = parse_block(l)?;
   Ok(ProcedureNode {
      name: extract_identifier(function_name),
      parameters,
      locals: HashMap::new(),
      block,
      ret_type,
      pure: false,
   })
}

fn parse_block(l: &mut Lexer) -> Result<BlockNode, ()> {
   expect(l, &Token::OpenBrace)?;

   let mut statements = vec![];

   loop {
      match l.peek() {
         Some(Token::OpenBrace) => {
            let new_block = parse_block(l)?;
            statements.push(Statement::BlockStatement(new_block));
         }
         Some(Token::CloseBrace) => {
            let _ = l.next();
            break;
         }
         Some(Token::KeywordReturn) => {
            let _ = l.next();
            let e = parse_expression(l)?;
            expect(l, &Token::Semicolon)?;
            statements.push(Statement::ReturnStatement(e));
         }
         Some(Token::KeywordLet) => {
            let mut declared_type = None;
            let _ = l.next();
            let variable_name = expect(l, &Token::Identifier(String::from("")))?;
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::Colon)) {
               let _ = l.next();
               declared_type = Some(parse_type(l)?);
            }
            expect(l, &Token::Assignment)?;
            let e = parse_expression(l)?;
            expect(l, &Token::Semicolon)?;
            statements.push(Statement::VariableDeclaration(
               extract_identifier(variable_name),
               e,
               declared_type,
            ));
         }
         Some(Token::KeywordIf) => {
            let s = parse_if_else_statement(l)?;
            statements.push(s);
         }
         Some(Token::BoolLiteral(_))
         | Some(Token::StringLiteral(_))
         | Some(Token::IntLiteral(_))
         | Some(Token::OpenParen)
         | Some(Token::Exclam)
         | Some(Token::Amp)
         | Some(Token::MultiplyDeref)
         | Some(Token::Identifier(_))
         | Some(Token::Minus) => {
            let e = parse_expression(l)?;
            match l.peek() {
               Some(&Token::Assignment) => {
                  let _ = l.next();
                  let re = parse_expression(l)?;
                  expect(l, &Token::Semicolon)?;
                  statements.push(Statement::AssignmentStatement(e, re));
               }
               Some(&Token::Semicolon) => {
                  let _ = l.next();
                  statements.push(Statement::ExpressionStatement(e));
               }
               x => {
                  eprintln!(
                     "While parsing statement - unexpected token {:?}; was expecting a semicolon or assignment operator",
                     x
                  );
                  return Err(());
               }
            }
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

fn parse_if_else_statement(l: &mut Lexer) -> Result<Statement, ()> {
   let _ = l.next();
   let e = parse_expression(l)?;
   let if_block = parse_block(l)?;
   let else_statement = match (l.peek(), l.double_peek()) {
      (Some(&Token::KeywordElse), Some(&Token::KeywordIf)) => {
         let _ = l.next();
         parse_if_else_statement(l)?
      }
      (Some(&Token::KeywordElse), _) => {
         let _ = l.next();
         Statement::BlockStatement(parse_block(l)?)
      }
      _ => Statement::BlockStatement(BlockNode { statements: vec![] }),
   };
   Ok(Statement::IfElseStatement(e, if_block, Box::new(else_statement)))
}

fn parse_parameters(l: &mut Lexer) -> Result<Vec<(String, ExpressionType)>, ()> {
   let mut parameters = vec![];

   loop {
      match l.peek() {
         Some(Token::Identifier(_)) => {
            let id = l.next().unwrap();
            expect(l, &Token::Colon)?;
            let e_type = parse_type(l)?;
            parameters.push((extract_identifier(id), e_type));
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::CloseParen)) {
               break;
            }
            expect(l, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         x => {
            eprintln!(
               "While parsing parameters - unexpected token {:?}; was expecting an identifier or a )",
               x
            );
            return Err(());
         }
      }
   }

   Ok(parameters)
}

fn parse_arguments(l: &mut Lexer) -> Result<Vec<ExpressionNode>, ()> {
   let mut arguments = vec![];

   loop {
      match l.peek() {
         Some(Token::Identifier(_))
         | Some(Token::BoolLiteral(_))
         | Some(Token::StringLiteral(_))
         | Some(Token::IntLiteral(_))
         | Some(Token::OpenParen)
         | Some(Token::Amp)
         | Some(Token::Exclam)
         | Some(Token::MultiplyDeref)
         | Some(Token::Minus) => {
            let e = parse_expression(l)?;
            arguments.push(e);
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::CloseParen)) {
               break;
            }
            expect(l, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         x => {
            eprintln!(
               "While parsing arguments - unexpected token {:?}; was expecting an expression or a )",
               x
            );
            return Err(());
         }
      }
   }

   Ok(arguments)
}

fn parse_expression(l: &mut Lexer) -> Result<ExpressionNode, ()> {
   Ok(wrap(pratt(l, 0)?))
}

fn parse_type(l: &mut Lexer) -> Result<ExpressionType, ()> {
   let mut ptr_count: usize = 0;
   while let Some(&Token::Amp) = l.peek() {
      ptr_count += 1;
      let _ = l.next();
   }
   let type_token = expect(l, &Token::Identifier(String::from("")))?;
   let type_s = extract_identifier(type_token);
   let value_type = match type_s.as_ref() {
      "bool" => ValueType::Bool,
      "i64" => crate::type_data::I64_TYPE,
      "i32" => crate::type_data::I32_TYPE,
      "i16" => crate::type_data::I16_TYPE,
      "i8" => crate::type_data::I8_TYPE,
      "u64" => crate::type_data::U64_TYPE,
      "u32" => crate::type_data::U32_TYPE,
      "u16" => crate::type_data::U16_TYPE,
      "u8" => crate::type_data::U8_TYPE,
      "String" => ValueType::String,
      x => {
         eprintln!("While parsing type, got an invalid type {}", x);
         return Err(());
      }
   };
   if ptr_count > 0 {
      Ok(ExpressionType::Pointer(ptr_count, value_type))
   } else {
      Ok(ExpressionType::Value(value_type))
   }
}

fn pratt(l: &mut Lexer, min_bp: u8) -> Result<Expression, ()> {
   println!("{:?}", l.peek());
   let lhs = l.next();
   let mut lhs = match lhs {
      Some(Token::BoolLiteral(x)) => Expression::BoolLiteral(x),
      Some(Token::IntLiteral(x)) => Expression::IntLiteral(x),
      Some(Token::StringLiteral(x)) => Expression::StringLiteral(x),
      Some(Token::Identifier(s)) => {
         if let Some(&Token::OpenParen) = l.peek() {
            let _ = l.next();
            let args = parse_arguments(l)?;
            expect(l, &Token::CloseParen)?;
            Expression::ProcedureCall(s, args)
         } else {
            Expression::Variable(s)
         }
      }
      Some(Token::OpenParen) => {
         let new_lhs = pratt(l, 0)?;
         expect(l, &Token::CloseParen)?;
         new_lhs
      }
      Some(x @ Token::Minus) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, r_bp)?;
         Expression::UnaryOperator(UnOp::Negate, Box::new(wrap(rhs)))
      }
      Some(x @ Token::Exclam) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, r_bp)?;
         Expression::UnaryOperator(UnOp::Complement, Box::new(wrap(rhs)))
      }
      Some(x @ Token::Amp) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, r_bp)?;
         Expression::UnaryOperator(UnOp::AddressOf, Box::new(wrap(rhs)))
      }
      Some(x @ Token::MultiplyDeref) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, r_bp)?;
         Expression::UnaryOperator(UnOp::Dereference, Box::new(wrap(rhs)))
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
      println!("{:?}", l.peek());
      let op: Token = match l.peek() {
         Some(x @ &Token::Plus)
         | Some(x @ &Token::Minus)
         | Some(x @ &Token::MultiplyDeref)
         | Some(x @ &Token::Divide)
         | Some(x @ &Token::LessThan)
         | Some(x @ &Token::LessThanOrEqualTo)
         | Some(x @ &Token::GreaterThan)
         | Some(x @ &Token::GreaterThanOrEqualTo)
         | Some(x @ &Token::Equality)
         | Some(x @ &Token::Pipe)
         | Some(x @ &Token::Amp)
         | Some(x @ &Token::Caret)
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
         Token::Pipe => BinOp::BitwiseOr,
         Token::Amp => BinOp::BitwiseAnd,
         Token::MultiplyDeref => BinOp::Multiply,
         Token::Divide => BinOp::Divide,
         Token::GreaterThan => BinOp::GreaterThan,
         Token::GreaterThanOrEqualTo => BinOp::GreaterThanOrEqualTo,
         Token::LessThan => BinOp::LessThan,
         Token::LessThanOrEqualTo => BinOp::LessThanOrEqualTo,
         Token::Equality => BinOp::Equality,
         Token::NotEquality => BinOp::NotEquality,
         Token::Caret => BinOp::BitwiseXor,
         _ => unreachable!(),
      };

      lhs = Expression::BinaryOperator(bin_op, Box::new((wrap(lhs), wrap(rhs))));
   }

   Ok(lhs)
}

fn prefix_binding_power(op: &Token) -> ((), u8) {
   match op {
      Token::Exclam => ((), 12),
      Token::Minus => ((), 12),
      Token::Amp => ((), 12),
      Token::MultiplyDeref => ((), 12),
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
      Token::Pipe => (2, 3),
      Token::Caret => (4, 5),
      Token::Amp => (6, 7),
      Token::Plus | Token::Minus => (8, 9),
      Token::MultiplyDeref | Token::Divide => (10, 11),
      _ => unreachable!(),
   }
}

fn wrap(expression: Expression) -> ExpressionNode {
   ExpressionNode {
      expression,
      exp_type: None,
   }
}
