use super::lex::{emit_source_info, SourceInfo, SourceToken, Token};
use crate::interner::{Interner, StrId, DUMMY_STR_TOKEN};
use crate::semantic_analysis::{EnumInfo, StaticInfo, StructInfo};
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
      let lex_token_str = lex_token.map(|x| x.token.for_parse_err()).unwrap_or("EOF");
      writeln!(
         err_stream,
         "Encountered '{}' when expecting '{}'",
         lex_token_str,
         token.for_parse_err()
      )
      .unwrap();
      if let Some(l_token) = lex_token {
         emit_source_info(err_stream, l_token.source_info);
      }
      return Err(());
   }
   Ok(lex_token.unwrap())
}

#[derive(Clone)]
pub struct ProcedureNode {
   pub name: StrId,
   pub parameters: Vec<ParameterNode>,
   pub locals: IndexMap<StrId, ExpressionType>,
   pub block: BlockNode,
   pub ret_type: ExpressionType,
   pub pure: bool,
   pub procedure_begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct ParameterNode {
   pub name: StrId,
   pub p_type: ExpressionType,
   pub named: bool,
}

#[derive(Clone)]
pub struct StructNode {
   pub name: StrId,
   pub fields: Vec<(StrId, ExpressionType)>,
   pub begin_location: SourceInfo,
}

#[derive(Clone)]
pub struct EnumNode {
   pub name: StrId,
   pub variants: Vec<StrId>,
   pub begin_location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct StaticNode {
   pub name: StrId,
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
   BitwiseLeftShift,
   BitwiseRightShift,
   LogicalAnd,
   LogicalOr,
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
   ProcedureCall(StrId, Box<[ArgumentNode]>),
   ArrayLiteral(Box<[ExpressionNode]>),
   ArrayIndex(Box<ExpressionNode>, Box<ExpressionNode>),
   BoolLiteral(bool),
   StringLiteral(StrId),
   IntLiteral(i64),
   FloatLiteral(f64),
   UnitLiteral,
   Variable(StrId),
   BinaryOperator(BinOp, Box<(ExpressionNode, ExpressionNode)>),
   UnaryOperator(UnOp, Box<ExpressionNode>),
   StructLiteral(StrId, Vec<(StrId, ExpressionNode)>),
   FieldAccess(Vec<StrId>, Box<ExpressionNode>),
   Extend(ExpressionType, Box<ExpressionNode>),
   Truncate(ExpressionType, Box<ExpressionNode>),
   Transmute(ExpressionType, Box<ExpressionNode>),
   EnumLiteral(StrId, StrId),
}

#[derive(Clone, Debug)]
pub struct ArgumentNode {
   pub name: Option<StrId>,
   pub expr: ExpressionNode,
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
   Assignment(ExpressionNode, ExpressionNode),
   Block(BlockNode),
   Loop(BlockNode),
   For(StrId, ExpressionNode, ExpressionNode, BlockNode),
   Continue,
   Break,
   Expression(ExpressionNode),
   IfElse(ExpressionNode, BlockNode, Box<StatementNode>),
   Return(ExpressionNode),
   VariableDeclaration(StrId, ExpressionNode, Option<ExpressionType>),
}

#[derive(Clone)]
pub struct BlockNode {
   pub statements: Vec<StatementNode>,
}

#[derive(Clone)]
pub struct Program {
   // These fields are populated by the parser
   pub enums: Vec<EnumNode>,
   pub procedures: Vec<ProcedureNode>,
   pub structs: Vec<StructNode>,
   pub statics: Vec<StaticNode>,

   // These fields are populated during semantic analysis
   pub literals: HashSet<StrId>,
   pub enum_info: IndexMap<StrId, EnumInfo>,
   pub struct_info: IndexMap<StrId, StructInfo>,
   pub static_info: IndexMap<StrId, StaticInfo>,
}

pub fn astify<W: Write>(tokens: Vec<SourceToken>, err_stream: &mut W, interner: &Interner) -> Result<Program, ()> {
   let mut lexer = Lexer::from_tokens(tokens);

   let mut procedures = vec![];
   let mut structs = vec![];
   let mut enums = vec![];
   let mut statics = vec![];

   while let Some(peeked_token) = lexer.peek_token() {
      match peeked_token {
         Token::KeywordFuncDef => {
            let def = lexer.next().unwrap();
            let mut p = parse_procedure(&mut lexer, err_stream, def.source_info, interner)?;
            p.pure = true;
            procedures.push(p);
         }
         Token::KeywordProcedureDef => {
            let def = lexer.next().unwrap();
            let p = parse_procedure(&mut lexer, err_stream, def.source_info, interner)?;
            procedures.push(p);
         }
         Token::KeywordStructDef => {
            let def = lexer.next().unwrap();
            let s = parse_struct(&mut lexer, err_stream, def.source_info, interner)?;
            structs.push(s);
         }
         Token::KeywordEnumDef => {
            let def = lexer.next().unwrap();
            let s = parse_enum(&mut lexer, err_stream, def.source_info, interner)?;
            enums.push(s);
         }
         Token::KeywordStatic => {
            let a_static = lexer.next().unwrap();
            let variable_name = expect(&mut lexer, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?;
            expect(&mut lexer, err_stream, &Token::Colon)?;
            let t_type = parse_type(&mut lexer, err_stream, interner)?;
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
               "While parsing top level - unexpected token '{}'; was expecting a function, procedure, or struct declaration",
               x.for_parse_err()
            ).unwrap();
            emit_source_info(err_stream, lexer.peek_source().unwrap());
            return Err(());
         }
      }
   }

   Ok(Program {
      procedures,
      enums,
      structs,
      statics,
      literals: HashSet::new(),
      struct_info: IndexMap::new(),
      static_info: IndexMap::new(),
      enum_info: IndexMap::new(),
   })
}

fn extract_identifier(t: Token) -> StrId {
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

fn parse_procedure<W: Write>(
   l: &mut Lexer,
   err_stream: &mut W,
   source_info: SourceInfo,
   interner: &Interner,
) -> Result<ProcedureNode, ()> {
   let function_name = expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?;
   expect(l, err_stream, &Token::OpenParen)?;
   let parameters = parse_parameters(l, err_stream, interner)?;
   expect(l, err_stream, &Token::CloseParen)?;
   let ret_type = if let Some(&Token::Arrow) = l.peek_token() {
      let _ = l.next();
      parse_type(l, err_stream, interner)?
   } else {
      ExpressionType::Value(ValueType::Unit)
   };
   let block = parse_block(l, err_stream, interner)?;
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

fn parse_struct<W: Write>(
   l: &mut Lexer,
   err_stream: &mut W,
   source_info: SourceInfo,
   interner: &Interner,
) -> Result<StructNode, ()> {
   let struct_name = extract_identifier(expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?.token);
   expect(l, err_stream, &Token::OpenBrace)?;
   let mut fields: Vec<(StrId, ExpressionType)> = vec![];
   loop {
      if let Some(&Token::CloseBrace) = l.peek_token() {
         let _ = l.next();
         break;
      }
      let identifier = expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?;
      let _ = expect(l, err_stream, &Token::Colon)?;
      let f_type = parse_type(l, err_stream, interner)?;
      fields.push((extract_identifier(identifier.token), f_type));
      if let Some(&Token::CloseBrace) = l.peek_token() {
         let _ = l.next();
         break;
      } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
         writeln!(err_stream, "While parsing definition of struct `{}`, encountered an unexpected identifier `{}`. Are you missing a comma?", interner.lookup(struct_name), interner.lookup(*x)).unwrap();
         emit_source_info(err_stream, l.peek_source().unwrap());
         return Result::Err(());
      } else {
         expect(l, err_stream, &Token::Comma)?;
      };
   }
   Ok(StructNode {
      name: struct_name,
      fields,
      begin_location: source_info,
   })
}

fn parse_enum<W: Write>(
   l: &mut Lexer,
   err_stream: &mut W,
   source_info: SourceInfo,
   interner: &Interner,
) -> Result<EnumNode, ()> {
   let enum_name = extract_identifier(expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?.token);
   expect(l, err_stream, &Token::OpenBrace)?;
   let mut variants: Vec<StrId> = vec![];
   loop {
      if let Some(&Token::CloseBrace) = l.peek_token() {
         let _ = l.next();
         break;
      }
      let identifier = expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?;
      variants.push(extract_identifier(identifier.token));
      if let Some(&Token::CloseBrace) = l.peek_token() {
         let _ = l.next();
         break;
      } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
         writeln!(err_stream, "While parsing definition of enum `{}`, encountered an unexpected identifier `{}`. Are you missing a comma?", interner.lookup(enum_name), interner.lookup(*x)).unwrap();
         emit_source_info(err_stream, l.peek_source().unwrap());
         return Result::Err(());
      } else {
         expect(l, err_stream, &Token::Comma)?;
      };
   }
   Ok(EnumNode {
      name: enum_name,
      variants,
      begin_location: source_info,
   })
}

fn parse_block<W: Write>(l: &mut Lexer, err_stream: &mut W, interner: &Interner) -> Result<BlockNode, ()> {
   expect(l, err_stream, &Token::OpenBrace)?;

   let mut statements: Vec<StatementNode> = vec![];

   loop {
      match l.peek_token() {
         Some(Token::OpenBrace) => {
            let source = l.peek_source().unwrap();
            let new_block = parse_block(l, err_stream, interner)?;
            statements.push(StatementNode {
               statement: Statement::Block(new_block),
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
               statement: Statement::Continue,
               statement_begin_location: continue_token.source_info,
            });
            expect(l, err_stream, &Token::Semicolon)?;
         }
         Some(Token::KeywordBreak) => {
            let break_token = l.next().unwrap();
            statements.push(StatementNode {
               statement: Statement::Break,
               statement_begin_location: break_token.source_info,
            });
            expect(l, err_stream, &Token::Semicolon)?;
         }
         Some(Token::KeywordFor) => {
            let for_token = l.next().unwrap();
            let variable_name = expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?;
            let _ = expect(l, err_stream, &Token::KeywordIn)?;
            let start_en = parse_expression(l, err_stream, true, interner)?;
            let _ = expect(l, err_stream, &Token::DoublePeriod)?;
            let end_en = parse_expression(l, err_stream, true, interner)?;
            let new_block = parse_block(l, err_stream, interner)?;
            statements.push(StatementNode {
               // TODO: instead of extracting here, we could preserve the source information and give better errors in the validator
               statement: Statement::For(extract_identifier(variable_name.token), start_en, end_en, new_block),
               statement_begin_location: for_token.source_info,
            });
         }
         Some(Token::KeywordLoop) => {
            let loop_token = l.next().unwrap();
            let new_block = parse_block(l, err_stream, interner)?;
            statements.push(StatementNode {
               statement: Statement::Loop(new_block),
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
               let e = parse_expression(l, err_stream, false, interner)?;
               expect(l, err_stream, &Token::Semicolon)?;
               e
            };
            statements.push(StatementNode {
               statement: Statement::Return(e),
               statement_begin_location: return_token.source_info,
            });
         }
         Some(Token::KeywordLet) => {
            let mut declared_type = None;
            let let_token = l.next().unwrap();
            let variable_name = expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?;
            let next_discrim = l.peek_token().map(discriminant);
            if next_discrim == Some(discriminant(&Token::Colon)) {
               let _ = l.next();
               declared_type = Some(parse_type(l, err_stream, interner)?);
            }
            expect(l, err_stream, &Token::Assignment)?;
            let e = parse_expression(l, err_stream, false, interner)?;
            expect(l, err_stream, &Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::VariableDeclaration(extract_identifier(variable_name.token), e, declared_type),
               statement_begin_location: let_token.source_info,
            });
         }
         Some(Token::KeywordIf) => {
            let s = parse_if_else_statement(l, err_stream, interner)?;
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
            let e = parse_expression(l, err_stream, false, interner)?;
            match l.peek_token() {
               Some(&Token::Assignment) => {
                  let _ = l.next();
                  let re = parse_expression(l, err_stream, false, interner)?;
                  expect(l, err_stream, &Token::Semicolon)?;
                  let statement_begin_location = e.expression_begin_location;
                  statements.push(StatementNode {
                     statement: Statement::Assignment(e, re),
                     statement_begin_location,
                  });
               }
               Some(&Token::Semicolon) => {
                  let _ = l.next();
                  let statement_begin_location = e.expression_begin_location;
                  statements.push(StatementNode {
                     statement: Statement::Expression(e),
                     statement_begin_location,
                  });
               }
               Some(x) => {
                  writeln!(
                     err_stream,
                     "While parsing statement - unexpected token '{}'; was expecting a semicolon or assignment operator",
                     x.for_parse_err()
                  ).unwrap();
                  emit_source_info(err_stream, l.peek_source().unwrap());
                  return Err(());
               }
               None => {
                  writeln!(
                     err_stream,
                     "While parsing statement - unexpected EOF; was expecting a semicolon or assignment operator",
                  )
                  .unwrap();
                  return Err(());
               }
            }
         }
         Some(x) => {
            writeln!(
               err_stream,
               "While parsing block - unexpected token '{}'; was expecting a statement",
               x.for_parse_err()
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

fn parse_if_else_statement<W: Write>(
   l: &mut Lexer,
   err_stream: &mut W,
   interner: &Interner,
) -> Result<StatementNode, ()> {
   let if_token = l.next().unwrap();
   let e = parse_expression(l, err_stream, true, interner)?;
   let if_block = parse_block(l, err_stream, interner)?;
   let else_statement = match (l.peek_token(), l.double_peek_token()) {
      (Some(&Token::KeywordElse), Some(&Token::KeywordIf)) => {
         let _ = l.next();
         parse_if_else_statement(l, err_stream, interner)?
      }
      (Some(&Token::KeywordElse), _) => {
         let else_token = l.next().unwrap();
         StatementNode {
            statement: Statement::Block(parse_block(l, err_stream, interner)?),
            statement_begin_location: else_token.source_info,
         }
      }
      _ => StatementNode {
         statement: Statement::Block(BlockNode { statements: vec![] }),
         statement_begin_location: if_token.source_info,
      },
   };
   Ok(StatementNode {
      statement: Statement::IfElse(e, if_block, Box::new(else_statement)),
      statement_begin_location: if_token.source_info,
   })
}

fn parse_parameters<W: Write>(
   l: &mut Lexer,
   err_stream: &mut W,
   interner: &Interner,
) -> Result<Vec<ParameterNode>, ()> {
   let mut parameters = vec![];

   loop {
      match l.peek_token() {
         Some(Token::Identifier(_)) | Some(Token::KeywordNamed) => {
            let named = if l.peek_token() == Some(&Token::KeywordNamed) {
               let _ = l.next();
               true
            } else {
               false
            };
            let id = l.next().unwrap();
            expect(l, err_stream, &Token::Colon)?;
            let e_type = parse_type(l, err_stream, interner)?;
            parameters.push(ParameterNode {
               name: extract_identifier(id.token),
               p_type: e_type,
               named,
            });
            if l.peek_token() == Some(&Token::CloseParen) {
               break;
            }
            expect(l, err_stream, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         Some(x) => {
            writeln!(
               err_stream,
               "While parsing parameters - unexpected token '{}'; was expecting an identifier or a )",
               x.for_parse_err()
            )
            .unwrap();
            emit_source_info(err_stream, l.peek_source().unwrap());
            return Err(());
         }
         None => {
            writeln!(
               err_stream,
               "While parsing parameters - unexpected token EOF; was expecting an identifier or a )",
            )
            .unwrap();
            return Err(());
         }
      }
   }

   Ok(parameters)
}

fn parse_arguments<W: Write>(l: &mut Lexer, err_stream: &mut W, interner: &Interner) -> Result<Vec<ArgumentNode>, ()> {
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
            let name: Option<StrId> = if let Some(Token::Identifier(x)) = l.peek_token().copied() {
               if l.double_peek_token() == Some(&Token::Colon) {
                  let _ = l.next();
                  let _ = l.next();
                  Some(x)
               } else {
                  None
               }
            } else {
               None
            };
            let expr = parse_expression(l, err_stream, false, interner)?;
            arguments.push(ArgumentNode { name, expr });
            let next_discrim = l.peek_token().map(discriminant);
            if next_discrim == Some(discriminant(&Token::CloseParen)) {
               break;
            }
            expect(l, err_stream, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         Some(x) => {
            writeln!(
               err_stream,
               "While parsing arguments - unexpected token '{}'; was expecting an expression or a )",
               x.for_parse_err()
            )
            .unwrap();
            emit_source_info(err_stream, l.peek_source().unwrap());
            return Err(());
         }
         None => {
            writeln!(
               err_stream,
               "While parsing arguments - unexpected EOF; was expecting an expression or a )",
            )
            .unwrap();
            return Err(());
         }
      }
   }

   Ok(arguments)
}

fn parse_expression<W: Write>(
   l: &mut Lexer,
   err_stream: &mut W,
   if_head: bool,
   interner: &Interner,
) -> Result<ExpressionNode, ()> {
   let begin_info = l.peek_source();
   let exp = pratt(l, err_stream, 0, if_head, interner)?;
   Ok(wrap(exp, begin_info.unwrap()))
}

fn parse_type<W: Write>(l: &mut Lexer, err_stream: &mut W, interner: &Interner) -> Result<ExpressionType, ()> {
   let mut ptr_count: usize = 0;
   while let Some(&Token::Amp) = l.peek_token() {
      ptr_count += 1;
      let _ = l.next();
   }

   let value_type = match l.peek_token() {
      Some(Token::OpenSquareBracket) => {
         let _ = l.next();
         let a_inner_type = parse_type(l, err_stream, interner)?;
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
         let type_token = expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?;
         let type_s = extract_identifier(type_token.token);
         match interner.lookup(type_s) {
            "bool" => ValueType::Bool,
            "isize" => crate::type_data::ISIZE_TYPE,
            "i64" => crate::type_data::I64_TYPE,
            "i32" => crate::type_data::I32_TYPE,
            "i16" => crate::type_data::I16_TYPE,
            "i8" => crate::type_data::I8_TYPE,
            "usize" => crate::type_data::USIZE_TYPE,
            "u64" => crate::type_data::U64_TYPE,
            "u32" => crate::type_data::U32_TYPE,
            "u16" => crate::type_data::U16_TYPE,
            "u8" => crate::type_data::U8_TYPE,
            "f32" => crate::type_data::F32_TYPE,
            "f64" => crate::type_data::F64_TYPE,
            _ => ValueType::Unresolved(type_s),
         }
      }
   };

   if ptr_count > 0 {
      Ok(ExpressionType::Pointer(ptr_count, value_type))
   } else {
      Ok(ExpressionType::Value(value_type))
   }
}

fn pratt<W: Write>(
   l: &mut Lexer,
   err_stream: &mut W,
   min_bp: u8,
   if_head: bool,
   interner: &Interner,
) -> Result<Expression, ()> {
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
            let args = parse_arguments(l, err_stream, interner)?;
            expect(l, err_stream, &Token::CloseParen)?;
            Expression::ProcedureCall(s, args.into_boxed_slice())
         } else if l.peek_token() == Some(&Token::DoubleColon) {
            let _ = l.next();
            let variant_identifier =
               extract_identifier(expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?.token);
            Expression::EnumLiteral(s, variant_identifier)
         } else if !if_head && l.peek_token() == Some(&Token::OpenBrace) {
            let _ = l.next();
            let mut fields = vec![];
            loop {
               if let Some(&Token::CloseBrace) = l.peek_token() {
                  let _ = l.next();
                  break;
               }
               let identifier = extract_identifier(expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?.token);
               let _ = expect(l, err_stream, &Token::Colon)?;
               let val = parse_expression(l, err_stream, false, interner)?;
               fields.push((identifier, val));
               if let Some(&Token::CloseBrace) = l.peek_token() {
                  let _ = l.next();
                  break;
               } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
                  let struct_str = interner.lookup(s);
                  let identifier_str = interner.lookup(*x);
                  writeln!(err_stream, "While parsing instantiation of struct `{}`, encountered an unexpected identifier `{}`. Are you missing a comma?", struct_str, identifier_str).unwrap();
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
            let new_lhs = pratt(l, err_stream, 0, false, interner)?;
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
            es.push(parse_expression(l, err_stream, false, interner)?);
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
         let rhs = pratt(l, err_stream, r_bp, if_head, interner)?;
         Expression::UnaryOperator(UnOp::Negate, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      Some(x @ Token::Exclam) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_stream, r_bp, if_head, interner)?;
         Expression::UnaryOperator(UnOp::Complement, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      Some(x @ Token::Amp) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_stream, r_bp, if_head, interner)?;
         Expression::UnaryOperator(UnOp::AddressOf, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      Some(x @ Token::MultiplyDeref) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_stream, r_bp, if_head, interner)?;
         Expression::UnaryOperator(UnOp::Dereference, Box::new(wrap(rhs, begin_location.unwrap())))
      }
      x => {
         let s = x.map(|x| x.for_parse_err()).unwrap_or("EOF");
         writeln!(
            err_stream,
            "While parsing expression - unexpected token '{}'; was expecting a literal, call, variable, or prefix operator",
            s
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
         | Some(x @ &Token::KeywordAnd)
         | Some(x @ &Token::KeywordOr)
         | Some(x @ &Token::Caret)
         | Some(x @ &Token::NotEquality)
         | Some(x @ &Token::KeywordExtend)
         | Some(x @ &Token::KeywordTruncate)
         | Some(x @ &Token::KeywordTransmute)
         | Some(x @ &Token::OpenSquareBracket)
         | Some(x @ &Token::ShiftLeft)
         | Some(x @ &Token::ShiftRight) => x,
         Some(&Token::Period) => {
            let mut fields = vec![];
            loop {
               let _ = l.next();
               fields.push(extract_identifier(
                  expect(l, err_stream, &Token::Identifier(DUMMY_STR_TOKEN))?.token,
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
               let inner = parse_expression(l, err_stream, false, interner)?;
               expect(l, err_stream, &Token::CloseSquareBracket)?;
               Expression::ArrayIndex(Box::new(wrap(lhs, lhs_source.unwrap())), Box::new(inner))
            }
            Token::KeywordExtend => {
               let a_type = parse_type(l, err_stream, interner)?;
               Expression::Extend(a_type, Box::new(wrap(lhs, lhs_source.unwrap())))
            }
            Token::KeywordTruncate => {
               let a_type = parse_type(l, err_stream, interner)?;
               Expression::Truncate(a_type, Box::new(wrap(lhs, lhs_source.unwrap())))
            }
            Token::KeywordTransmute => {
               let a_type = parse_type(l, err_stream, interner)?;
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
      let rhs = pratt(l, err_stream, r_b, if_head, interner)?;

      let bin_op = match op {
         Token::Plus => BinOp::Add,
         Token::Minus => BinOp::Subtract,
         Token::Pipe => BinOp::BitwiseOr,
         Token::Amp => BinOp::BitwiseAnd,
         Token::KeywordOr => BinOp::LogicalOr,
         Token::KeywordAnd => BinOp::LogicalAnd,
         Token::MultiplyDeref => BinOp::Multiply,
         Token::Divide => BinOp::Divide,
         Token::Remainder => BinOp::Remainder,
         Token::GreaterThan => BinOp::GreaterThan,
         Token::GreaterThanOrEqualTo => BinOp::GreaterThanOrEqualTo,
         Token::LessThan => BinOp::LessThan,
         Token::LessThanOrEqualTo => BinOp::LessThanOrEqualTo,
         Token::ShiftLeft => BinOp::BitwiseLeftShift,
         Token::ShiftRight => BinOp::BitwiseRightShift,
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
      Token::Exclam => ((), 17),
      Token::Minus => ((), 17),
      Token::Amp => ((), 17),
      Token::MultiplyDeref => ((), 17),
      _ => unreachable!(),
   }
}

fn postfix_binding_power(op: &Token) -> Option<(u8, ())> {
   match &op {
      Token::OpenSquareBracket => Some((20, ())),
      Token::KeywordExtend => Some((18, ())),
      Token::KeywordTruncate => Some((18, ())),
      Token::KeywordTransmute => Some((18, ())),
      _ => None,
   }
}

fn infix_binding_power(op: &Token) -> (u8, u8) {
   match &op {
      Token::KeywordOr => (1, 2),
      Token::KeywordAnd => (3, 4),
      Token::Equality
      | Token::NotEquality
      | Token::GreaterThan
      | Token::GreaterThanOrEqualTo
      | Token::LessThan
      | Token::LessThanOrEqualTo => (5, 5),
      Token::Pipe => (6, 7),
      Token::Caret => (8, 9),
      Token::Amp => (10, 11),
      Token::ShiftLeft | Token::ShiftRight => (12, 13),
      Token::Plus | Token::Minus => (14, 15),
      Token::MultiplyDeref | Token::Divide | Token::Remainder => (16, 17),
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
