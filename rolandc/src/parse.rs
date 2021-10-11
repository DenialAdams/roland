use super::lex::{emit_source_info, SourceInfo, SourceToken, Token};
use crate::semantic_analysis::{StaticInfo, StructInfo};
use crate::type_data::{ExpressionType, ValueType};
use indexmap::IndexMap;
use std::collections::HashSet;
use std::io::Write;
use std::mem::discriminant;

struct Lexer {
   tokens: Vec<SourceToken>,
}

impl Lexer {
   fn from_tokens(mut tokens: Vec<SourceToken>) -> Lexer {
      tokens.reverse();
      Lexer { tokens }
   }

   fn peek_source(&self) -> Option<SourceInfo> {
      self.tokens.last().map(|x| x.source_info)
   }

   fn peek_token(&self) -> Option<&Token> {
      self.tokens.last().map(|x| &x.token)
   }

   fn double_peek_token(&self) -> Option<&Token> {
      if self.tokens.len() <= 1 {
         return None;
      }

      self.tokens.get(self.tokens.len() - 2).map(|x| &x.token)
   }

   fn next(&mut self) -> Option<SourceToken> {
      self.tokens.pop()
   }
}

fn expect<W: Write>(l: &mut Lexer, err_stream: &mut W, token: &Token) -> Result<SourceToken, ()> {
   let lex_token = l.next();
   if lex_token
      .as_ref()
      .map(|x| discriminant(&x.token) != discriminant(token))
      .unwrap_or(true)
   {
      writeln!(err_stream, "got {:?} when expecting {:?}", lex_token, token).unwrap();
      if let Some(l_token) = lex_token {
         emit_source_info(err_stream, l_token.source_info);
      }
      return Err(());
   }
   Ok(lex_token.unwrap())
}

#[derive(Clone)]
pub struct ProcedureNode {
   pub name: String,
   pub parameters: Vec<(String, ExpressionType)>,
   pub locals: IndexMap<String, ExpressionType>,
   pub block: BlockNode,
   pub ret_type: ExpressionType,
   pub pure: bool,
   pub procedure_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct StructNode {
   pub name: String,
   pub fields: Vec<(String, ExpressionType)>,
   pub struct_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct StaticNode {
   pub name: String,
   pub static_type: ExpressionType,
   pub static_begin_location: SourceInfo,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BinOp {
   Add,
   Subtract,
   Multiply,
   Divide,
   Remainder,
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

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum UnOp {
   Negate,
   Complement,
   AddressOf,
   Dereference,
}

#[derive(Clone, Debug)]
pub struct ExpressionNode {
   pub expression: Expression,
   pub exp_type: Option<ExpressionType>,
   pub expression_begin_location: SourceInfo,
}

#[derive(Clone, Debug)]
pub enum Expression {
   ProcedureCall(String, Box<[ExpressionNode]>),
   ArrayLiteral(Box<[ExpressionNode]>),
   ArrayIndex(Box<ExpressionNode>, Box<ExpressionNode>),
   BoolLiteral(bool),
   StringLiteral(String),
   IntLiteral(i64),
   FloatLiteral(f64),
   UnitLiteral,
   Variable(String),
   BinaryOperator(BinOp, Box<(ExpressionNode, ExpressionNode)>),
   UnaryOperator(UnOp, Box<ExpressionNode>),
   StructLiteral(String, Vec<(String, ExpressionNode)>),
   FieldAccess(Vec<String>, Box<ExpressionNode>),
   Extend(ExpressionType, Box<ExpressionNode>),
   Truncate(ExpressionType, Box<ExpressionNode>),
   Transmute(ExpressionType, Box<ExpressionNode>),
}

impl Expression {
   pub fn is_lvalue(&self) -> bool {
      match self {
         Expression::Variable(_) => true,
         Expression::ArrayIndex(array_exp, _) => array_exp.expression.is_lvalue(),
         Expression::UnaryOperator(UnOp::Dereference, _) => true,
         Expression::FieldAccess(_, lhs) => lhs.expression.is_lvalue(),
         _ => false,
      }
   }
}

#[derive(Clone)]
pub struct StatementNode {
   pub statement: Statement,
   pub statement_begin_location: SourceInfo,
}

#[derive(Clone)]
pub enum Statement {
   AssignmentStatement(ExpressionNode, ExpressionNode),
   BlockStatement(BlockNode),
   LoopStatement(BlockNode),
   ContinueStatement,
   BreakStatement,
   ExpressionStatement(ExpressionNode),
   IfElseStatement(ExpressionNode, BlockNode, Box<StatementNode>),
   ReturnStatement(ExpressionNode),
   VariableDeclaration(String, ExpressionNode, Option<ExpressionType>),
}

#[derive(Clone)]
pub struct BlockNode {
   pub statements: Vec<StatementNode>,
}

#[derive(Clone)]
pub struct Program {
   pub procedures: Vec<ProcedureNode>,
   pub structs: Vec<StructNode>,
   pub statics: Vec<StaticNode>,

   // These fields are populated by the semantic phase
   pub literals: HashSet<String>,
   pub struct_info: IndexMap<String, StructInfo>,
   pub static_info: IndexMap<String, StaticInfo>,
}

pub fn astify<W: Write>(tokens: Vec<SourceToken>, err_stream: &mut W) -> Result<Program, ()> {
   let mut lexer = Lexer::from_tokens(tokens);

   let mut procedures = vec![];
   let mut structs = vec![];
   let mut statics = vec![];

   while let Some(peeked_token) = lexer.peek_token() {
      match peeked_token {
         Token::KeywordFuncDef => {
            let def = lexer.next().unwrap();
            let mut p = parse_procedure(&mut lexer, err_stream, def.source_info)?;
            p.pure = true;
            procedures.push(p);
         }
         Token::KeywordProcedureDef => {
            let def = lexer.next().unwrap();
            let p = parse_procedure(&mut lexer, err_stream, def.source_info)?;
            procedures.push(p);
         }
         Token::KeywordStructDef => {
            let def = lexer.next().unwrap();
            let s = parse_struct(&mut lexer, err_stream, def.source_info)?;
            structs.push(s);
         }
         Token::KeywordStatic => {
            let a_static = lexer.next().unwrap();
            let variable_name = expect(&mut lexer, err_stream, &Token::Identifier(String::from("")))?;
            expect(&mut lexer, err_stream, &Token::Colon)?;
            let t_type = parse_type(&mut lexer, err_stream)?;
            expect(&mut lexer, err_stream, &Token::Semicolon)?;
            statics.push(StaticNode {
               name: extract_identifier(variable_name.token),
               static_type: t_type,
               static_begin_location: a_static.source_info,
            });
         }
         x => {
            writeln!(
               err_stream,
               "While parsing top level - unexpected token {:?}; was expecting a function, procedure, or struct declaration",
               x
            ).unwrap();
            emit_source_info(err_stream, lexer.peek_source().unwrap());
            return Err(());
         }
      }
   }

   Ok(Program {
      procedures,
      structs,
      statics,
      literals: HashSet::new(),
      struct_info: IndexMap::new(),
      static_info: IndexMap::new(),
   })
}

fn extract_identifier(t: Token) -> String {
   match t {
      Token::Identifier(v) => v,
      _ => unreachable!(),
   }
}

fn extract_int_literal(t: Token) -> i64 {
   match t {
      Token::IntLiteral(v) => v,
      _ => unreachable!(),
   }
}

fn parse_procedure<W: Write>(l: &mut Lexer, err_stream: &mut W, source_info: SourceInfo) -> Result<ProcedureNode, ()> {
   let function_name = expect(l, err_stream, &Token::Identifier(String::from("")))?;
   expect(l, err_stream, &Token::OpenParen)?;
   let parameters = parse_parameters(l, err_stream)?;
   expect(l, err_stream, &Token::CloseParen)?;
   let ret_type = if let Some(&Token::Arrow) = l.peek_token() {
      let _ = l.next();
      parse_type(l, err_stream)?
   } else {
      ExpressionType::Value(ValueType::Unit)
   };
   let block = parse_block(l, err_stream)?;
   Ok(ProcedureNode {
      name: extract_identifier(function_name.token),
      parameters,
      locals: IndexMap::new(),
      block,
      ret_type,
      pure: false,
      procedure_begin_location: source_info,
   })
}

fn parse_struct<W: Write>(l: &mut Lexer, err_stream: &mut W, source_info: SourceInfo) -> Result<StructNode, ()> {
   let struct_name = extract_identifier(expect(l, err_stream, &Token::Identifier(String::from("")))?.token);
   expect(l, err_stream, &Token::OpenBrace)?;
   let mut fields: Vec<(String, ExpressionType)> = vec![];
   loop {
      if let Some(&Token::CloseBrace) = l.peek_token() {
         let _ = l.next();
         break;
      }
      let identifier = expect(l, err_stream, &Token::Identifier(String::from("")))?;
      let _ = expect(l, err_stream, &Token::Colon)?;
      let f_type = parse_type(l, err_stream)?;
      fields.push((extract_identifier(identifier.token), f_type));
      if let Some(&Token::CloseBrace) = l.peek_token() {
         let _ = l.next();
         break;
      } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
         writeln!(err_stream, "While parsing definition of struct `{}`, encountered an unexpected identifier `{}`. Are you missing a comma?", struct_name, x).unwrap();
         emit_source_info(err_stream, l.peek_source().unwrap());
         return Result::Err(());
      } else {
         expect(l, err_stream, &Token::Comma)?;
      };
   }
   Ok(StructNode {
      name: struct_name,
      fields,
      struct_begin_location: source_info,
   })
}

fn parse_block<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<BlockNode, ()> {
   expect(l, err_stream, &Token::OpenBrace)?;

   let mut statements: Vec<StatementNode> = vec![];

   loop {
      match l.peek_token() {
         Some(Token::OpenBrace) => {
            let source = l.peek_source().unwrap();
            let new_block = parse_block(l, err_stream)?;
            statements.push(StatementNode {
               statement: Statement::BlockStatement(new_block),
               statement_begin_location: source,
            });
         }
         Some(Token::CloseBrace) => {
            let _ = l.next();
            break;
         }
         Some(Token::KeywordContinue) => {
            let continue_token = l.next().unwrap();
            statements.push(StatementNode {
               statement: Statement::ContinueStatement,
               statement_begin_location: continue_token.source_info,
            });
            expect(l, err_stream, &Token::Semicolon)?;
         }
         Some(Token::KeywordBreak) => {
            let break_token = l.next().unwrap();
            statements.push(StatementNode {
               statement: Statement::BreakStatement,
               statement_begin_location: break_token.source_info,
            });
            expect(l, err_stream, &Token::Semicolon)?;
         }
         Some(Token::KeywordLoop) => {
            let loop_token = l.next().unwrap();
            let new_block = parse_block(l, err_stream)?;
            statements.push(StatementNode {
               statement: Statement::LoopStatement(new_block),
               statement_begin_location: loop_token.source_info,
            });
         }
         Some(Token::KeywordReturn) => {
            let return_token = l.next().unwrap();
            let e = if let Some(Token::Semicolon) = l.peek_token() {
               let _ = l.next().unwrap();
               ExpressionNode {
                  expression: Expression::UnitLiteral,
                  exp_type: None,
                  expression_begin_location: return_token.source_info,
               }
            } else {
               let e = parse_expression(l, err_stream, false)?;
               expect(l, err_stream, &Token::Semicolon)?;
               e
            };
            statements.push(StatementNode {
               statement: Statement::ReturnStatement(e),
               statement_begin_location: return_token.source_info,
            });
         }
         Some(Token::KeywordLet) => {
            let mut declared_type = None;
            let let_token = l.next().unwrap();
            let variable_name = expect(l, err_stream, &Token::Identifier(String::from("")))?;
            let next_discrim = l.peek_token().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::Colon)) {
               let _ = l.next();
               declared_type = Some(parse_type(l, err_stream)?);
            }
            expect(l, err_stream, &Token::Assignment)?;
            let e = parse_expression(l, err_stream, false)?;
            expect(l, err_stream, &Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::VariableDeclaration(extract_identifier(variable_name.token), e, declared_type),
               statement_begin_location: let_token.source_info,
            });
         }
         Some(Token::KeywordIf) => {
            let s = parse_if_else_statement(l, err_stream)?;
            statements.push(s);
         }
         Some(Token::BoolLiteral(_))
         | Some(Token::StringLiteral(_))
         | Some(Token::IntLiteral(_))
         | Some(Token::FloatLiteral(_))
         | Some(Token::OpenParen)
         | Some(Token::Exclam)
         | Some(Token::Amp)
         | Some(Token::MultiplyDeref)
         | Some(Token::Identifier(_))
         | Some(Token::Minus) => {
            let e = parse_expression(l, err_stream, false)?;
            match l.peek_token() {
               Some(&Token::Assignment) => {
                  let _ = l.next();
                  let re = parse_expression(l, err_stream, false)?;
                  expect(l, err_stream, &Token::Semicolon)?;
                  let statement_begin_location = e.expression_begin_location;
                  statements.push(StatementNode {
                     statement: Statement::AssignmentStatement(e, re),
                     statement_begin_location,
                  });
               }
               Some(&Token::Semicolon) => {
                  let _ = l.next();
                  let statement_begin_location = e.expression_begin_location;
                  statements.push(StatementNode {
                     statement: Statement::ExpressionStatement(e),
                     statement_begin_location,
                  });
               }
               x => {
                  writeln!(
                     err_stream,
                     "While parsing statement - unexpected token {:?}; was expecting a semicolon or assignment operator",
                     x
                  ).unwrap();
                  if let Some(si) = l.peek_source() {
                     emit_source_info(err_stream, si);
                  }
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
            emit_source_info(err_stream, l.peek_source().unwrap());
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

fn parse_if_else_statement<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<StatementNode, ()> {
   let if_token = l.next().unwrap();
   let e = parse_expression(l, err_stream, true)?;
   let if_block = parse_block(l, err_stream)?;
   let else_statement = match (l.peek_token(), l.double_peek_token()) {
      (Some(&Token::KeywordElse), Some(&Token::KeywordIf)) => {
         let _ = l.next();
         parse_if_else_statement(l, err_stream)?
      }
      (Some(&Token::KeywordElse), _) => {
         let else_token = l.next().unwrap();
         StatementNode {
            statement: Statement::BlockStatement(parse_block(l, err_stream)?),
            statement_begin_location: else_token.source_info,
         }
      }
      _ => StatementNode {
         statement: Statement::BlockStatement(BlockNode { statements: vec![] }),
         statement_begin_location: if_token.source_info,
      },
   };
   Ok(StatementNode {
      statement: Statement::IfElseStatement(e, if_block, Box::new(else_statement)),
      statement_begin_location: if_token.source_info,
   })
}

fn parse_parameters<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<Vec<(String, ExpressionType)>, ()> {
   let mut parameters = vec![];

   loop {
      match l.peek_token() {
         Some(Token::Identifier(_)) => {
            let id = l.next().unwrap();
            expect(l, err_stream, &Token::Colon)?;
            let e_type = parse_type(l, err_stream)?;
            parameters.push((extract_identifier(id.token), e_type));
            let next_discrim = l.peek_token().map(|x| discriminant(x));
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
            if let Some(si) = l.peek_source() {
               emit_source_info(err_stream, si);
            }
            return Err(());
         }
      }
   }

   Ok(parameters)
}

fn parse_arguments<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<Vec<ExpressionNode>, ()> {
   let mut arguments = vec![];

   loop {
      match l.peek_token() {
         Some(Token::Identifier(_))
         | Some(Token::BoolLiteral(_))
         | Some(Token::StringLiteral(_))
         | Some(Token::IntLiteral(_))
         | Some(Token::FloatLiteral(_))
         | Some(Token::OpenParen)
         | Some(Token::OpenSquareBracket)
         | Some(Token::Amp)
         | Some(Token::Exclam)
         | Some(Token::MultiplyDeref)
         | Some(Token::Minus) => {
            let e = parse_expression(l, err_stream, false)?;
            arguments.push(e);
            let next_discrim = l.peek_token().map(|x| discriminant(x));
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
            if let Some(si) = l.peek_source() {
               emit_source_info(err_stream, si);
            }
            return Err(());
         }
      }
   }

   Ok(arguments)
}

fn parse_expression<W: Write>(l: &mut Lexer, err_stream: &mut W, if_head: bool) -> Result<ExpressionNode, ()> {
   let begin_info = l.peek_source();
   let exp = pratt(l, err_stream, 0, if_head)?;
   Ok(wrap(exp, begin_info.unwrap()))
}

fn parse_type<W: Write>(l: &mut Lexer, err_stream: &mut W) -> Result<ExpressionType, ()> {
   let mut ptr_count: usize = 0;
   while let Some(&Token::Amp) = l.peek_token() {
      ptr_count += 1;
      let _ = l.next();
   }

   let value_type = match l.peek_token() {
      Some(Token::OpenSquareBracket) => {
         let _ = l.next();
         let a_inner_type = parse_type(l, err_stream)?;
         expect(l, err_stream, &Token::Semicolon)?;
         let length = expect(l, err_stream, &Token::IntLiteral(0))?;
         expect(l, err_stream, &Token::CloseSquareBracket)?;
         ValueType::Array(Box::new(a_inner_type), extract_int_literal(length.token))
      }
      Some(Token::OpenParen) => {
         let _ = l.next();
         expect(l, err_stream, &Token::CloseParen)?;
         ValueType::Unit
      }
      _ => {
         let type_token = expect(l, err_stream, &Token::Identifier(String::from("")))?;
         let type_s = extract_identifier(type_token.token);
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
            "f32" => crate::type_data::F32_TYPE,
            "f64" => crate::type_data::F64_TYPE,
            _ => ValueType::Struct(type_s),
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
   let lhs_token = l.next();
   let lhs_source = lhs_token.as_ref().map(|x| x.source_info);
   let mut lhs = match lhs_token.map(|x| x.token) {
      Some(Token::BoolLiteral(x)) => Expression::BoolLiteral(x),
      Some(Token::IntLiteral(x)) => Expression::IntLiteral(x),
      Some(Token::FloatLiteral(x)) => Expression::FloatLiteral(x),
      Some(Token::StringLiteral(x)) => Expression::StringLiteral(x),
      Some(Token::Identifier(s)) => {
         if l.peek_token() == Some(&Token::OpenParen) {
            let _ = l.next();
            let args = parse_arguments(l, err_stream)?;
            expect(l, err_stream, &Token::CloseParen)?;
            Expression::ProcedureCall(s, args.into_boxed_slice())
         } else if !if_head && l.peek_token() == Some(&Token::OpenBrace) {
            let _ = l.next();
            let mut fields = vec![];
            loop {
               if let Some(&Token::CloseBrace) = l.peek_token() {
                  let _ = l.next();
                  break;
               }
               let identifier = extract_identifier(expect(l, err_stream, &Token::Identifier(String::from("")))?.token);
               let _ = expect(l, err_stream, &Token::Colon)?;
               let val = parse_expression(l, err_stream, false)?;
               fields.push((identifier, val));
               if let Some(&Token::CloseBrace) = l.peek_token() {
                  let _ = l.next();
                  break;
               } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
                  writeln!(err_stream, "While parsing instantiation of struct `{}`, encountered an unexpected identifier `{}`. Are you missing a comma?", s, x).unwrap();
                  emit_source_info(err_stream, l.peek_source().unwrap());
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
         if let Some(&Token::CloseParen) = l.peek_token() {
            let _ = l.next();
            Expression::UnitLiteral
         } else {
            let new_lhs = pratt(l, err_stream, 0, false)?;
            expect(l, err_stream, &Token::CloseParen)?;
            new_lhs
         }
      }
      Some(Token::OpenSquareBracket) => {
         // Array creation
         let mut es = vec![];
         loop {
            if let Some(Token::CloseSquareBracket) = l.peek_token() {
               break;
            }
            es.push(parse_expression(l, err_stream, false)?);
            if let Some(Token::CloseSquareBracket) = l.peek_token() {
               break;
            } else {
               expect(l, err_stream, &Token::Comma)?;
            }
         }
         let _ = l.next(); // ]
         Expression::ArrayLiteral(es.into_boxed_slice())
      }
      Some(x @ Token::Minus) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::Negate, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      Some(x @ Token::Exclam) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::Complement, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      Some(x @ Token::Amp) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::AddressOf, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      Some(x @ Token::MultiplyDeref) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_stream, r_bp, if_head)?;
         Expression::UnaryOperator(UnOp::Dereference, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      x => {
         writeln!(
            err_stream,
            "While parsing expression - unexpected token {:?}; was expecting a literal, call, variable, or prefix operator",
            x
         )
         .unwrap();
         if let Some(si) = l.peek_source() {
            emit_source_info(err_stream, si);
         }
         return Err(());
      }
   };

   loop {
      let op: &Token = match l.peek_token() {
         Some(x @ &Token::Plus)
         | Some(x @ &Token::Minus)
         | Some(x @ &Token::MultiplyDeref)
         | Some(x @ &Token::Divide)
         | Some(x @ &Token::Remainder)
         | Some(x @ &Token::LessThan)
         | Some(x @ &Token::LessThanOrEqualTo)
         | Some(x @ &Token::GreaterThan)
         | Some(x @ &Token::GreaterThanOrEqualTo)
         | Some(x @ &Token::Equality)
         | Some(x @ &Token::Pipe)
         | Some(x @ &Token::Amp)
         | Some(x @ &Token::Caret)
         | Some(x @ &Token::NotEquality)
         | Some(x @ &Token::KeywordExtend)
         | Some(x @ &Token::KeywordTruncate)
         | Some(x @ &Token::KeywordTransmute)
         | Some(x @ &Token::OpenSquareBracket) => x,
         Some(&Token::Period) => {
            let mut fields = vec![];
            loop {
               let _ = l.next();
               fields.push(extract_identifier(
                  expect(l, err_stream, &Token::Identifier(String::from("")))?.token,
               ));
               if l.peek_token() != Some(&Token::Period) {
                  break;
               }
            }
            lhs = Expression::FieldAccess(fields, Box::new(wrap(lhs, lhs_source.unwrap())));
            continue;
         }
         _ => break,
      };

      if let Some((l_bp, ())) = postfix_binding_power(op) {
         if l_bp < min_bp {
            break;
         }

         let op = l.next().unwrap().token;

         lhs = match op {
            Token::OpenSquareBracket => {
               let inner = parse_expression(l, err_stream, false)?;
               expect(l, err_stream, &Token::CloseSquareBracket)?;
               Expression::ArrayIndex(Box::new(wrap(lhs, lhs_source.unwrap())), Box::new(inner))
            }
            Token::KeywordExtend => {
               let a_type = parse_type(l, err_stream)?;
               Expression::Extend(a_type, Box::new(wrap(lhs, lhs_source.unwrap())))
            }
            Token::KeywordTruncate => {
               let a_type = parse_type(l, err_stream)?;
               Expression::Truncate(a_type, Box::new(wrap(lhs, lhs_source.unwrap())))
            }
            Token::KeywordTransmute => {
               let a_type = parse_type(l, err_stream)?;
               Expression::Transmute(a_type, Box::new(wrap(lhs, lhs_source.unwrap())))
            }
            _ => unreachable!(),
         };

         continue;
      }

      let (l_bp, r_b) = infix_binding_power(op);
      if l_bp < min_bp {
         break;
      }

      let next_token = l.next().unwrap();
      let op = next_token.token;
      let rhs = pratt(l, err_stream, r_b, if_head)?;

      let bin_op = match op {
         Token::Plus => BinOp::Add,
         Token::Minus => BinOp::Subtract,
         Token::Pipe => BinOp::BitwiseOr,
         Token::Amp => BinOp::BitwiseAnd,
         Token::MultiplyDeref => BinOp::Multiply,
         Token::Divide => BinOp::Divide,
         Token::Remainder => BinOp::Remainder,
         Token::GreaterThan => BinOp::GreaterThan,
         Token::GreaterThanOrEqualTo => BinOp::GreaterThanOrEqualTo,
         Token::LessThan => BinOp::LessThan,
         Token::LessThanOrEqualTo => BinOp::LessThanOrEqualTo,
         Token::Equality => BinOp::Equality,
         Token::NotEquality => BinOp::NotEquality,
         Token::Caret => BinOp::BitwiseXor,
         _ => unreachable!(),
      };

      lhs = Expression::BinaryOperator(
         bin_op,
         Box::new((wrap(lhs, lhs_source.unwrap()), wrap(rhs, next_token.source_info))),
      );
   }

   Ok(lhs)
}

fn prefix_binding_power(op: &Token) -> ((), u8) {
   match op {
      Token::Exclam => ((), 13),
      Token::Minus => ((), 13),
      Token::Amp => ((), 13),
      Token::MultiplyDeref => ((), 13),
      _ => unreachable!(),
   }
}

fn postfix_binding_power(op: &Token) -> Option<(u8, ())> {
   match &op {
      Token::OpenSquareBracket => Some((14, ())),
      Token::KeywordExtend => Some((12, ())),
      Token::KeywordTruncate => Some((12, ())),
      Token::KeywordTransmute => Some((12, ())),
      _ => None,
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
      Token::MultiplyDeref | Token::Divide | Token::Remainder => (10, 11),
      _ => unreachable!(),
   }
}

fn wrap(expression: Expression, source_info: SourceInfo) -> ExpressionNode {
   ExpressionNode {
      expression,
      exp_type: None,
      expression_begin_location: source_info,
   }
}
