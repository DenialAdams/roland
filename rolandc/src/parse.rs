use super::lex::Token;
use crate::type_data::{ExpressionType, ValueType};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::mem::discriminant;
use indexmap::IndexMap;

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

fn expect<W: Write>(l: &mut Lexer, err_stream: &mut W, token: &Token) -> Result<Token, ()> {
   let lex_token = l.next();
   if lex_token
      .as_ref()
      .map(|x| discriminant(x) != discriminant(token))
      .unwrap_or(true)
   {
      writeln!(err_stream, "got {:?} when expecting {:?}", lex_token, token).unwrap();
      return Err(());
   }
   Ok(lex_token.unwrap())
}

pub struct ProcedureNode {
   pub name: String,
   pub parameters: Vec<(String, ExpressionType)>,
   pub locals: IndexMap<String, ExpressionType>,
   pub block: BlockNode,
   pub ret_type: ExpressionType,
   pub pure: bool,
}

pub struct StructNode {
   pub name: String,
   pub fields: Vec<(String, ExpressionType)>,
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
   UnitLiteral,
   Variable(String),
   BinaryOperator(BinOp, Box<(ExpressionNode, ExpressionNode)>),
   UnaryOperator(UnOp, Box<ExpressionNode>),
   StructLiteral(String, Vec<(String, ExpressionNode)>),
   FieldAccess(Vec<String>, Box<ExpressionNode>),
}

impl Expression {
   pub fn is_lvalue(&self) -> bool {
      match self {
         Expression::Variable(_) => true,
         Expression::UnaryOperator(UnOp::Dereference, _) => true,
         Expression::FieldAccess(_, _) => true,
         _ => false,
      }
   }
}

pub enum Statement {
   AssignmentStatement(ExpressionNode, ExpressionNode),
   BlockStatement(BlockNode),
   LoopStatement(BlockNode),
   ContinueStatement,
   BreakStatement,
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
   pub structs: Vec<StructNode>,

   // These fields are populated by the semantic phase
   pub literals: HashSet<String>,
   pub struct_info: IndexMap<String, HashMap<String, ExpressionType>>,
}

pub fn astify<W: Write>(tokens: Vec<Token>, err_stream: &mut W) -> Result<Program, ()> {
   let mut lexer = Lexer::from_tokens(tokens);

   let mut procedures = vec![];
   let mut structs = vec![];

   while let Some(peeked_token) = lexer.peek() {
      match peeked_token {
         Token::KeywordFuncDef => {
            let _ = lexer.next();
            let mut p = parse_procedure(&mut lexer, err_stream)?;
            p.pure = true;
            procedures.push(p);
         }
         Token::KeywordProcedureDef => {
            let _ = lexer.next();
            let p = parse_procedure(&mut lexer, err_stream)?;
            procedures.push(p);
         }
         Token::KeywordStructDef => {
            let _ = lexer.next();
            let s = parse_struct(&mut lexer, err_stream)?;
            structs.push(s);
         }
         x => {
            writeln!(
               err_stream,
               "While parsing top level - unexpected token {:?}; was expecting a function, procedure, or struct declaration",
               x
            ).unwrap();
            return Err(());
         }
      }
   }

   Ok(Program {
      procedures,
      structs,
      literals: HashSet::new(),
      struct_info: IndexMap::new(),
   })
}

fn extract_identifier(t: Token) -> String {
   match t {
      Token::Identifier(v) => v,
      _ => unreachable!(),
   }
}

fn parse_procedure<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<ProcedureNode, ()> {
   let function_name = expect(l, err_stream, &Token::Identifier(String::from("")))?;
   expect(l, err_stream, &Token::OpenParen)?;
   let parameters = parse_parameters(l, err_stream)?;
   expect(l, err_stream, &Token::CloseParen)?;
   let ret_type = if let Some(&Token::Arrow) = l.peek() {
      let _ = l.next();
      parse_type(l, err_stream)?
   } else {
      ExpressionType::Value(ValueType::Unit)
   };
   let block = parse_block(l, err_stream)?;
   Ok(ProcedureNode {
      name: extract_identifier(function_name),
      parameters,
      locals: IndexMap::new(),
      block,
      ret_type,
      pure: false,
   })
}

fn parse_struct<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<StructNode, ()> {
   let struct_name = extract_identifier(expect(l, err_stream, &Token::Identifier(String::from("")))?);
   expect(l, err_stream, &Token::OpenBrace)?;
   let mut fields: Vec<(String, ExpressionType)> = vec![];
   loop {
      if let Some(&Token::CloseBrace) = l.peek() {
         let _ = l.next();
         break;
      }
      let identifier = expect(l, err_stream, &Token::Identifier(String::from("")))?;
      let _ = expect(l, err_stream, &Token::Colon)?;
      let f_type = parse_type(l, err_stream)?;
      fields.push((extract_identifier(identifier), f_type));
      if let Some(&Token::CloseBrace) = l.peek() {
         let _ = l.next();
         break;
      } else if let Some(&Token::Identifier(x)) = l.peek().as_ref() {
         writeln!(err_stream, "While parsing definition of struct `{}`, encountered an unexpected identifier `{}`. Are you missing a comma?", struct_name, x).unwrap();
         return Result::Err(());
      } else {
         expect(l, err_stream, &Token::Comma)?;
      };
   }
   Ok(StructNode {
      name: struct_name,
      fields,
   })
}

fn parse_block<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<BlockNode, ()> {
   expect(l, err_stream, &Token::OpenBrace)?;

   let mut statements = vec![];

   loop {
      match l.peek() {
         Some(Token::OpenBrace) => {
            let new_block = parse_block(l, err_stream)?;
            statements.push(Statement::BlockStatement(new_block));
         }
         Some(Token::CloseBrace) => {
            let _ = l.next();
            break;
         }
         Some(Token::KeywordContinue) => {
            let _ = l.next();
            statements.push(Statement::ContinueStatement);
            expect(l, err_stream, &Token::Semicolon)?;
         }
         Some(Token::KeywordBreak) => {
            let _ = l.next();
            statements.push(Statement::BreakStatement);
            expect(l, err_stream, &Token::Semicolon)?;
         }
         Some(Token::KeywordLoop) => {
            let _ = l.next();
            let new_block = parse_block(l, err_stream)?;
            statements.push(Statement::LoopStatement(new_block));
         }
         Some(Token::KeywordReturn) => {
            let _ = l.next();
            let e = if let Some(Token::Semicolon) = l.peek() {
               let _ = l.next();
               wrap(Expression::UnitLiteral)
            } else {
               let e = parse_expression(l, err_stream, false)?;
               expect(l, err_stream, &Token::Semicolon)?;
               e
            };
            statements.push(Statement::ReturnStatement(e));
         }
         Some(Token::KeywordLet) => {
            let mut declared_type = None;
            let _ = l.next();
            let variable_name = expect(l, err_stream, &Token::Identifier(String::from("")))?;
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::Colon)) {
               let _ = l.next();
               declared_type = Some(parse_type(l, err_stream)?);
            }
            expect(l, err_stream, &Token::Assignment)?;
            let e = parse_expression(l, err_stream, false)?;
            expect(l, err_stream, &Token::Semicolon)?;
            statements.push(Statement::VariableDeclaration(
               extract_identifier(variable_name),
               e,
               declared_type,
            ));
         }
         Some(Token::KeywordIf) => {
            let s = parse_if_else_statement(l, err_stream)?;
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
            let e = parse_expression(l, err_stream, false)?;
            match l.peek() {
               Some(&Token::Assignment) => {
                  let _ = l.next();
                  let re = parse_expression(l, err_stream, false)?;
                  expect(l, err_stream, &Token::Semicolon)?;
                  statements.push(Statement::AssignmentStatement(e, re));
               }
               Some(&Token::Semicolon) => {
                  let _ = l.next();
                  statements.push(Statement::ExpressionStatement(e));
               }
               x => {
                  writeln!(
                     err_stream,
                     "While parsing statement - unexpected token {:?}; was expecting a semicolon or assignment operator",
                     x
                  ).unwrap();
                  return Err(());
               }
            }
         }
         Some(x) => {
            writeln!(
               err_stream,
               "While parsing block - unexpected token {:?}; was expecting a statement",
               x
            )
            .unwrap();
            return Err(());
         }
         None => {
            writeln!(
               err_stream,
               "While parsing block - unexpected EOF; was expecting a statement or a }}"
            )
            .unwrap();
            return Err(());
         }
      }
   }
   Ok(BlockNode { statements })
}

fn parse_if_else_statement<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<Statement, ()> {
   let _ = l.next();
   let e = parse_expression(l, err_stream, true)?;
   let if_block = parse_block(l, err_stream)?;
   let else_statement = match (l.peek(), l.double_peek()) {
      (Some(&Token::KeywordElse), Some(&Token::KeywordIf)) => {
         let _ = l.next();
         parse_if_else_statement(l, err_stream)?
      }
      (Some(&Token::KeywordElse), _) => {
         let _ = l.next();
         Statement::BlockStatement(parse_block(l, err_stream)?)
      }
      _ => Statement::BlockStatement(BlockNode { statements: vec![] }),
   };
   Ok(Statement::IfElseStatement(e, if_block, Box::new(else_statement)))
}

fn parse_parameters<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<Vec<(String, ExpressionType)>, ()> {
   let mut parameters = vec![];

   loop {
      match l.peek() {
         Some(Token::Identifier(_)) => {
            let id = l.next().unwrap();
            expect(l, err_stream, &Token::Colon)?;
            let e_type = parse_type(l, err_stream)?;
            parameters.push((extract_identifier(id), e_type));
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::CloseParen)) {
               break;
            }
            expect(l, err_stream, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         x => {
            writeln!(
               err_stream,
               "While parsing parameters - unexpected token {:?}; was expecting an identifier or a )",
               x
            )
            .unwrap();
            return Err(());
         }
      }
   }

   Ok(parameters)
}

fn parse_arguments<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<Vec<ExpressionNode>, ()> {
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
            let e = parse_expression(l, err_stream, false)?;
            arguments.push(e);
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::CloseParen)) {
               break;
            }
            expect(l, err_stream, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         x => {
            writeln!(
               err_stream,
               "While parsing arguments - unexpected token {:?}; was expecting an expression or a )",
               x
            )
            .unwrap();
            return Err(());
         }
      }
   }

   Ok(arguments)
}

fn parse_expression<W: Write>(l: &mut Lexer, err_stream: &mut W, if_head: bool) -> Result<ExpressionNode, ()> {
   Ok(wrap(pratt(l, err_stream, 0, if_head)?))
}

fn parse_type<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<ExpressionType, ()> {
   let mut ptr_count: usize = 0;
   while let Some(&Token::Amp) = l.peek() {
      ptr_count += 1;
      let _ = l.next();
   }

   let value_type = match l.peek() {
      Some(Token::OpenParen) => {
         let _ = l.next();
         expect(l, err_stream, &Token::CloseParen)?;
         ValueType::Unit
      }
      _ => {
         let type_token = expect(l, err_stream, &Token::Identifier(String::from("")))?;
         let type_s = extract_identifier(type_token);
         match type_s.as_ref() {
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
            _ => ValueType::Struct(type_s)
         }
      }
   };

   if ptr_count > 0 {
      Ok(ExpressionType::Pointer(ptr_count, value_type))
   } else {
      Ok(ExpressionType::Value(value_type))
   }
}

fn pratt<W: Write>(l: &mut Lexer, err_stream: &mut W, min_bp: u8, if_head: bool) -> Result<Expression, ()> {
   let lhs = l.next();
   let mut lhs = match lhs {
      Some(Token::BoolLiteral(x)) => Expression::BoolLiteral(x),
      Some(Token::IntLiteral(x)) => Expression::IntLiteral(x),
      Some(Token::StringLiteral(x)) => Expression::StringLiteral(x),
      Some(Token::Identifier(s)) => {
         if l.peek() == Some(&Token::OpenParen)  {
            let _ = l.next();
            let args = parse_arguments(l, err_stream)?;
            expect(l, err_stream, &Token::CloseParen)?;
            Expression::ProcedureCall(s, args)
         } else if !if_head && l.peek() == Some(&Token::OpenBrace) {
            let _ = l.next();
            let mut fields = vec![];
            loop {
               if let Some(&Token::CloseBrace) = l.peek() {
                  let _ = l.next();
                  break;
               }
               let identifier = extract_identifier(expect(l, err_stream, &Token::Identifier(String::from("")))?);
               let _ = expect(l, err_stream, &Token::Colon)?;
               let val = parse_expression(l, err_stream, false)?;
               fields.push((identifier, val));
               if let Some(&Token::CloseBrace) = l.peek() {
                  let _ = l.next();
                  break;
               } else if let Some(&Token::Identifier(x)) = l.peek().as_ref() {
                  writeln!(err_stream, "While parsing instantiation of struct `{}`, encountered an unexpected identifier `{}`. Are you missing a comma?", s, x).unwrap();
                  return Result::Err(());
               } else {
                  expect(l, err_stream, &Token::Comma)?;
               };
            }
            Expression::StructLiteral(s, fields)
         } else {
            Expression::Variable(s)
         }
      }
      Some(Token::OpenParen) => {
         if let Some(&Token::CloseParen) = l.peek() {
            let _ = l.next();
            Expression::UnitLiteral
         } else {
            let new_lhs = pratt(l, err_stream, 0, false)?;
            expect(l, err_stream, &Token::CloseParen)?;
            new_lhs
         }
      }
      Some(x @ Token::Minus) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::Negate, Box::new(wrap(rhs)))
      }
      Some(x @ Token::Exclam) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::Complement, Box::new(wrap(rhs)))
      }
      Some(x @ Token::Amp) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::AddressOf, Box::new(wrap(rhs)))
      }
      Some(x @ Token::MultiplyDeref) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::Dereference, Box::new(wrap(rhs)))
      }
      x => {
         writeln!(
            err_stream,
            "While parsing expression - unexpected token {:?}; was expecting a literal, call, variable, or prefix operator",
            x
         )
         .unwrap();
         return Err(());
      }
   };

   loop {
      let op: &Token = match l.peek() {
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
         | Some(x @ &Token::NotEquality) => x,
         Some(&Token::Period) => {
            let mut fields = vec![];
            loop {
               let _ = l.next();
               fields.push(extract_identifier(expect(l, err_stream, &Token::Identifier(String::from("")))?));
               if l.peek() != Some(&Token::Period) {
                  break;
               }
            }
            lhs = Expression::FieldAccess(fields, Box::new(wrap(lhs)));
            continue;
         },
         _ => break,
      };

      let (l_bp, r_b) = infix_binding_power(op);
      if l_bp < min_bp {
         break;
      }

      let op = l.next().unwrap();
      let rhs = pratt(l, err_stream, r_b, if_head)?;

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
      _ => unreachable!(),
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
