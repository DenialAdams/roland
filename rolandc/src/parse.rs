use super::lex::{SourceInfo, SourceToken, Token};
use crate::error_handling::error_handling_macros::{rolandc_error, rolandc_error_no_loc};
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId, DUMMY_STR_TOKEN};
use crate::semantic_analysis::{EnumInfo, StaticInfo, StructInfo};
use crate::size_info::SizeInfo;
use crate::type_data::{ExpressionType, ValueType};
use crate::typed_index_vec::{Handle, HandleMap};
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};
use std::mem::discriminant;

pub type ExpressionPool = HandleMap<ExpressionId, ExpressionNode>;

fn merge_locations(begin: SourceInfo, end: SourceInfo) -> SourceInfo {
   SourceInfo {
      begin: begin.begin,
      end: end.end,
      file: begin.file,
   }
}

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
      // TODO: We probably can just copy this instead of returning a reference now
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

fn expect(l: &mut Lexer, err_manager: &mut ErrorManager, token: &Token) -> Result<SourceToken, ()> {
   let lex_token = l.next();
   if lex_token
      .as_ref()
      .map_or(true, |x| discriminant(&x.token) != discriminant(token))
   {
      if let Some(l_token) = lex_token {
         rolandc_error!(
            err_manager,
            l_token.source_info,
            "Encountered '{}' when expecting '{}'",
            l_token.token.for_parse_err(),
            token.for_parse_err()
         );
      } else {
         rolandc_error_no_loc!(
            err_manager,
            "Encountered 'EOF' when expecting '{}'",
            token.for_parse_err()
         );
      }
      return Err(());
   }
   Ok(lex_token.unwrap())
}

#[derive(Clone)]
pub struct ProcedureDefinition {
   pub name: StrId,
   pub parameters: Vec<ParameterNode>,
   pub ret_type: ExpressionType,
}

#[derive(Clone)]
pub struct ProcedureNode {
   pub definition: ProcedureDefinition,
   pub block: BlockNode,
   pub location: SourceInfo,

   // TODO: if we use id-s for types (ala strings), we could use tinyset?
   pub locals: IndexMap<StrId, HashSet<ExpressionType>>,
   pub virtual_locals: IndexSet<ExpressionId>,
}

#[derive(Clone)]
pub enum ProcImplSource {
   Builtin,
   External,
}

#[derive(Clone)]
pub struct ExternalProcedureNode {
   pub definition: ProcedureDefinition,
   pub location: SourceInfo,
   pub impl_source: ProcImplSource,
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
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct EnumNode {
   pub name: StrId,
   pub variants: Vec<StrId>,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct ConstNode {
   pub name: IdentifierNode,
   pub const_type: ExpressionType,
   pub value: ExpressionId,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct StaticNode {
   pub name: IdentifierNode,
   pub static_type: ExpressionType,
   pub value: Option<ExpressionId>,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct ExpressionTypeNode {
   pub e_type: ExpressionType,
   pub location: SourceInfo,
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
   pub location: SourceInfo,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExpressionId(usize);

impl Handle for ExpressionId {
   fn new(x: usize) -> Self {
      ExpressionId(x)
   }

   fn index(self) -> usize {
      self.0
   }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
   ProcedureCall {
      proc_name: StrId,
      generic_args: Box<[GenericArgumentNode]>,
      args: Box<[ArgumentNode]>,
   },
   ArrayLiteral(Box<[ExpressionId]>),
   ArrayIndex {
      array: ExpressionId,
      index: ExpressionId,
   },
   BoolLiteral(bool),
   StringLiteral(StrId),
   IntLiteral(i128),
   FloatLiteral(f64),
   UnitLiteral,
   Variable(StrId),
   BinaryOperator {
      operator: BinOp,
      lhs: ExpressionId,
      rhs: ExpressionId,
   },
   UnaryOperator(UnOp, ExpressionId),
   StructLiteral(StrId, Vec<(StrId, ExpressionId)>),
   FieldAccess(Vec<StrId>, ExpressionId),
   Extend(ExpressionType, ExpressionId),
   Truncate(ExpressionType, ExpressionId),
   Transmute(ExpressionType, ExpressionId),
   EnumLiteral(StrId, StrId),
}

// TODO: it would be cool if StrId was NonZero so that this struct (and others like it)
// could be smaller
#[derive(Clone, Debug, PartialEq)]
pub struct ArgumentNode {
   pub name: Option<StrId>,
   pub expr: ExpressionId,
}

#[derive(Clone, Debug, PartialEq)]
pub struct GenericArgumentNode {
   pub gtype: ExpressionType,
}

impl Expression {
   pub fn is_lvalue(&self, expressions: &ExpressionPool, static_info: &IndexMap<StrId, StaticInfo>) -> bool {
      match self {
         Expression::Variable(x) => static_info.get(x).map_or(true, |x| !x.is_const),
         Expression::ArrayIndex { array, .. } => expressions[*array].expression.is_lvalue(expressions, static_info),
         Expression::UnaryOperator(UnOp::Dereference, _) => true,
         Expression::FieldAccess(_, lhs) => expressions[*lhs].expression.is_lvalue(expressions, static_info),
         _ => false,
      }
   }

   // After constants are lowered, we don't need to care about constants and pass a bulky data structure around
   pub fn is_lvalue_disregard_consts(&self, expressions: &ExpressionPool) -> bool {
      match self {
         Expression::Variable(_) => true,
         Expression::ArrayIndex { array, .. } => expressions[*array].expression.is_lvalue_disregard_consts(expressions),
         Expression::UnaryOperator(UnOp::Dereference, _) => true,
         Expression::FieldAccess(_, lhs) => expressions[*lhs].expression.is_lvalue_disregard_consts(expressions),
         _ => false,
      }
   }
}

#[derive(Clone)]
pub struct StatementNode {
   pub statement: Statement,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub enum Statement {
   Assignment(ExpressionId, ExpressionId),
   Block(BlockNode),
   Loop(BlockNode),
   For(IdentifierNode, ExpressionId, ExpressionId, BlockNode, bool),
   Continue,
   Break,
   Expression(ExpressionId),
   // TODO: banish this Box. The type is misleading here, because an if else always has either a block or another if-else,
   // so we should try to rectify that too.
   IfElse(ExpressionId, BlockNode, Box<StatementNode>),
   Return(ExpressionId),
   VariableDeclaration(IdentifierNode, ExpressionId, Option<ExpressionType>),
}

#[derive(Clone, Debug)]
pub struct IdentifierNode {
   pub identifier: StrId,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct ImportNode {
   pub import_path: StrId,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct BlockNode {
   pub statements: Vec<StatementNode>,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct Program {
   // These fields are populated by the parser
   pub enums: Vec<EnumNode>,
   pub external_procedures: Vec<ExternalProcedureNode>,
   pub procedures: Vec<ProcedureNode>,
   pub structs: Vec<StructNode>,
   pub consts: Vec<ConstNode>,
   pub statics: Vec<StaticNode>,

   // These fields are populated during semantic analysis
   pub literals: IndexSet<StrId>,
   pub enum_info: IndexMap<StrId, EnumInfo>,
   pub struct_info: IndexMap<StrId, StructInfo>,
   pub static_info: IndexMap<StrId, StaticInfo>,
   pub struct_size_info: HashMap<StrId, SizeInfo>,
}

impl Program {
   pub fn new() -> Program {
      Program {
         enums: Vec::new(),
         external_procedures: Vec::new(),
         procedures: Vec::new(),
         structs: Vec::new(),
         consts: Vec::new(),
         statics: Vec::new(),
         literals: IndexSet::new(),
         enum_info: IndexMap::new(),
         struct_info: IndexMap::new(),
         static_info: IndexMap::new(),
         struct_size_info: HashMap::new(),
      }
   }
}

pub fn astify(
   tokens: Vec<SourceToken>,
   err_manager: &mut ErrorManager,
   interner: &Interner,
   expressions: &mut ExpressionPool,
) -> Result<(Vec<ImportNode>, Program), ()> {
   let mut lexer = Lexer::from_tokens(tokens);

   let mut external_procedures = vec![];
   let mut procedures = vec![];
   let mut structs = vec![];
   let mut enums = vec![];
   let mut consts = vec![];
   let mut statics = vec![];
   let mut imports = vec![];

   while let Some(peeked_token) = lexer.peek_token() {
      match peeked_token {
         Token::KeywordExtern => {
            let extern_kw = lexer.next().unwrap();
            expect(&mut lexer, err_manager, &Token::KeywordProcedureDef)?;
            let p = parse_external_procedure(
               &mut lexer,
               err_manager,
               extern_kw.source_info,
               interner,
               ProcImplSource::External,
            )?;
            external_procedures.push(p);
         }
         Token::KeywordBuiltin => {
            let builtin_kw = lexer.next().unwrap();
            expect(&mut lexer, err_manager, &Token::KeywordProcedureDef)?;
            let p = parse_external_procedure(
               &mut lexer,
               err_manager,
               builtin_kw.source_info,
               interner,
               ProcImplSource::Builtin,
            )?;
            external_procedures.push(p);
         }
         Token::KeywordProcedureDef => {
            let def = lexer.next().unwrap();
            let p = parse_procedure(&mut lexer, err_manager, def.source_info, expressions, interner)?;
            procedures.push(p);
         }
         Token::KeywordImport => {
            let kw = lexer.next().unwrap();
            let import_token = expect(&mut lexer, err_manager, &Token::StringLiteral(DUMMY_STR_TOKEN))?;
            let sc = expect(&mut lexer, err_manager, &Token::Semicolon)?;
            imports.push(ImportNode {
               import_path: extract_str_literal(import_token.token),
               location: merge_locations(kw.source_info, sc.source_info),
            });
         }
         Token::KeywordStructDef => {
            let def = lexer.next().unwrap();
            let s = parse_struct(&mut lexer, err_manager, def.source_info, interner)?;
            structs.push(s);
         }
         Token::KeywordEnumDef => {
            let def = lexer.next().unwrap();
            let s = parse_enum(&mut lexer, err_manager, def.source_info, interner)?;
            enums.push(s);
         }
         Token::KeywordConst => {
            let a_const = lexer.next().unwrap();
            let variable_name = expect(&mut lexer, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
            expect(&mut lexer, err_manager, &Token::Colon)?;
            let t_type = parse_type(&mut lexer, err_manager, interner)?;
            expect(&mut lexer, err_manager, &Token::Assignment)?;
            let exp = parse_expression(&mut lexer, err_manager, false, expressions, interner)?;
            let end_token = expect(&mut lexer, err_manager, &Token::Semicolon)?;
            consts.push(ConstNode {
               name: IdentifierNode {
                  identifier: extract_identifier(variable_name.token),
                  location: variable_name.source_info,
               },
               const_type: t_type.e_type,
               location: merge_locations(a_const.source_info, end_token.source_info),
               value: exp,
            });
         }
         Token::KeywordStatic => {
            let a_static = lexer.next().unwrap();
            let variable_name = expect(&mut lexer, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
            expect(&mut lexer, err_manager, &Token::Colon)?;
            let t_type = parse_type(&mut lexer, err_manager, interner)?;
            let exp = if lexer.peek_token() == Some(&Token::Assignment) {
               let _ = lexer.next();
               Some(parse_expression(&mut lexer, err_manager, false, expressions, interner)?)
            } else {
               None
            };
            let end_token = expect(&mut lexer, err_manager, &Token::Semicolon)?;
            statics.push(StaticNode {
               name: IdentifierNode {
                  identifier: extract_identifier(variable_name.token),
                  location: variable_name.source_info,
               },
               static_type: t_type.e_type,
               location: merge_locations(a_static.source_info, end_token.source_info),
               value: exp,
            });
         }
         x => {
            rolandc_error!(
               err_manager,
               lexer.peek_source().unwrap(),
               "While parsing top level - unexpected token '{}'; was expecting a procedure, const, static, enum, or struct declaration",
               x.for_parse_err()
            );
            return Err(());
         }
      }
   }

   Ok((
      imports,
      Program {
         external_procedures,
         procedures,
         enums,
         structs,
         consts,
         statics,
         literals: IndexSet::new(),
         struct_info: IndexMap::new(),
         static_info: IndexMap::new(),
         enum_info: IndexMap::new(),
         struct_size_info: HashMap::new(),
      },
   ))
}

fn extract_identifier(t: Token) -> StrId {
   match t {
      Token::Identifier(v) => v,
      _ => unreachable!(),
   }
}

fn extract_str_literal(t: Token) -> StrId {
   match t {
      Token::StringLiteral(v) => v,
      _ => unreachable!(),
   }
}

fn extract_int_literal(t: Token) -> i128 {
   match t {
      Token::IntLiteral(v) => v,
      _ => unreachable!(),
   }
}

fn parse_procedure(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   source_info: SourceInfo,
   expressions: &mut ExpressionPool,
   interner: &Interner,
) -> Result<ProcedureNode, ()> {
   let procedure_name = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
   expect(l, err_manager, &Token::OpenParen)?;
   let parameters = parse_parameters(l, err_manager, interner)?;
   expect(l, err_manager, &Token::CloseParen)?;
   let ret_type = if let Some(&Token::Arrow) = l.peek_token() {
      let _ = l.next();
      parse_type(l, err_manager, interner)?.e_type
   } else {
      ExpressionType::Value(ValueType::Unit)
   };
   let block = parse_block(l, err_manager, expressions, interner)?;
   let combined_location = merge_locations(source_info, block.location);
   Ok(ProcedureNode {
      definition: ProcedureDefinition {
         name: extract_identifier(procedure_name.token),
         parameters,
         ret_type,
      },
      locals: IndexMap::new(),
      virtual_locals: IndexSet::new(),
      block,
      location: combined_location,
   })
}

fn parse_external_procedure(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   source_info: SourceInfo,
   interner: &Interner,
   proc_impl_source: ProcImplSource,
) -> Result<ExternalProcedureNode, ()> {
   let procedure_name = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
   expect(l, err_manager, &Token::OpenParen)?;
   let parameters = parse_parameters(l, err_manager, interner)?;
   expect(l, err_manager, &Token::CloseParen)?;
   let ret_type = if let Some(&Token::Arrow) = l.peek_token() {
      let _ = l.next();
      parse_type(l, err_manager, interner)?.e_type
   } else {
      ExpressionType::Value(ValueType::Unit)
   };
   let end_token = expect(l, err_manager, &Token::Semicolon)?;
   Ok(ExternalProcedureNode {
      definition: ProcedureDefinition {
         name: extract_identifier(procedure_name.token),
         parameters,
         ret_type,
      },
      location: merge_locations(source_info, end_token.source_info),
      impl_source: proc_impl_source,
   })
}

fn parse_struct(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   source_info: SourceInfo,
   interner: &Interner,
) -> Result<StructNode, ()> {
   let struct_name = extract_identifier(expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?.token);
   expect(l, err_manager, &Token::OpenBrace)?;
   let mut fields: Vec<(StrId, ExpressionType)> = vec![];
   loop {
      if let Some(&Token::CloseBrace) = l.peek_token() {
         break;
      }
      let identifier = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
      let _ = expect(l, err_manager, &Token::Colon)?;
      let f_type = parse_type(l, err_manager, interner)?.e_type;
      fields.push((extract_identifier(identifier.token), f_type));
      if let Some(&Token::CloseBrace) = l.peek_token() {
         break;
      } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
         rolandc_error!(
            err_manager,
            l.peek_source().unwrap(),
            "While parsing definition of struct `{}`, encountered an unexpected identifier `{}`. Hint: Are you missing a comma?",
            interner.lookup(struct_name),
            interner.lookup(*x),
         );
         return Result::Err(());
      }
      expect(l, err_manager, &Token::Comma)?;
   }
   let close_brace = l.next().unwrap();
   Ok(StructNode {
      name: struct_name,
      fields,
      location: merge_locations(source_info, close_brace.source_info),
   })
}

fn parse_enum(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   source_info: SourceInfo,
   interner: &Interner,
) -> Result<EnumNode, ()> {
   let enum_name = extract_identifier(expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?.token);
   expect(l, err_manager, &Token::OpenBrace)?;
   let mut variants: Vec<StrId> = vec![];
   loop {
      if let Some(&Token::CloseBrace) = l.peek_token() {
         break;
      }
      let identifier = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
      variants.push(extract_identifier(identifier.token));
      if let Some(&Token::CloseBrace) = l.peek_token() {
         break;
      } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
         rolandc_error!(
            err_manager,
            l.peek_source().unwrap(),
            "While parsing definition of enum `{}`, encountered an unexpected identifier `{}`. Hint: Are you missing a comma?",
            interner.lookup(enum_name),
            interner.lookup(*x),
         );
         return Result::Err(());
      }

      expect(l, err_manager, &Token::Comma)?;
   }
   let close_brace = l.next().unwrap();
   Ok(EnumNode {
      name: enum_name,
      variants,
      location: merge_locations(source_info, close_brace.source_info),
   })
}

fn parse_block(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   expressions: &mut ExpressionPool,
   interner: &Interner,
) -> Result<BlockNode, ()> {
   let open_brace = expect(l, err_manager, &Token::OpenBrace)?;

   let mut statements: Vec<StatementNode> = vec![];

   loop {
      match l.peek_token() {
         Some(Token::OpenBrace) => {
            let source = l.peek_source().unwrap();
            let new_block = parse_block(l, err_manager, expressions, interner)?;
            statements.push(StatementNode {
               statement: Statement::Block(new_block),
               location: source,
            });
         }
         Some(Token::CloseBrace) => {
            break;
         }
         Some(Token::KeywordContinue) => {
            let continue_token = l.next().unwrap();
            let sc = expect(l, err_manager, &Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::Continue,
               location: merge_locations(continue_token.source_info, sc.source_info),
            });
         }
         Some(Token::KeywordBreak) => {
            let break_token = l.next().unwrap();
            let sc = expect(l, err_manager, &Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::Break,
               location: merge_locations(break_token.source_info, sc.source_info),
            });
         }
         Some(Token::KeywordFor) => {
            let for_token = l.next().unwrap();
            let variable_name = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
            let _ = expect(l, err_manager, &Token::KeywordIn)?;
            let start_en = parse_expression(l, err_manager, true, expressions, interner)?;
            let _ = expect(l, err_manager, &Token::DoublePeriod)?;
            let inclusive = if l.peek_token() == Some(&Token::Assignment) {
               let _ = l.next();
               true
            } else {
               false
            };
            let end_en = parse_expression(l, err_manager, true, expressions, interner)?;
            let new_block = parse_block(l, err_manager, expressions, interner)?;
            statements.push(StatementNode {
               statement: Statement::For(
                  IdentifierNode {
                     location: variable_name.source_info,
                     identifier: extract_identifier(variable_name.token),
                  },
                  start_en,
                  end_en,
                  new_block,
                  inclusive,
               ),
               location: for_token.source_info,
            });
         }
         Some(Token::KeywordLoop) => {
            let loop_token = l.next().unwrap();
            let new_block = parse_block(l, err_manager, expressions, interner)?;
            statements.push(StatementNode {
               statement: Statement::Loop(new_block),
               location: loop_token.source_info,
            });
         }
         Some(Token::KeywordReturn) => {
            let return_token = l.next().unwrap();
            let e = if let Some(Token::Semicolon) = l.peek_token() {
               wrap(Expression::UnitLiteral, return_token.source_info, expressions)
            } else {
               parse_expression(l, err_manager, false, expressions, interner)?
            };
            let sc = expect(l, err_manager, &Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::Return(e),
               location: merge_locations(return_token.source_info, sc.source_info),
            });
         }
         Some(Token::KeywordLet) => {
            let mut declared_type = None;
            let let_token = l.next().unwrap();
            let variable_name = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
            let next_discrim = l.peek_token().map(discriminant);
            if next_discrim == Some(discriminant(&Token::Colon)) {
               let _ = l.next();
               declared_type = Some(parse_type(l, err_manager, interner)?);
            }
            expect(l, err_manager, &Token::Assignment)?;
            let e = parse_expression(l, err_manager, false, expressions, interner)?;
            let sc = expect(l, err_manager, &Token::Semicolon)?;
            let statement_location = merge_locations(let_token.source_info, sc.source_info);
            statements.push(StatementNode {
               statement: Statement::VariableDeclaration(
                  IdentifierNode {
                     identifier: extract_identifier(variable_name.token),
                     location: variable_name.source_info,
                  },
                  e,
                  declared_type.map(|x| x.e_type),
               ),
               location: statement_location,
            });
         }
         Some(Token::KeywordIf) => {
            let s = parse_if_else_statement(l, err_manager, expressions, interner)?;
            statements.push(s);
         }
         Some(
            Token::BoolLiteral(_)
            | Token::StringLiteral(_)
            | Token::IntLiteral(_)
            | Token::FloatLiteral(_)
            | Token::OpenParen
            | Token::Exclam
            | Token::Amp
            | Token::MultiplyDeref
            | Token::Identifier(_)
            | Token::Minus,
         ) => {
            let e = parse_expression(l, err_manager, false, expressions, interner)?;
            match l.peek_token() {
               Some(&Token::Assignment) => {
                  let _ = l.next();
                  let re = parse_expression(l, err_manager, false, expressions, interner)?;
                  let sc = expect(l, err_manager, &Token::Semicolon)?;
                  let statement_location = merge_locations(expressions[e].location, sc.source_info);
                  statements.push(StatementNode {
                     statement: Statement::Assignment(e, re),
                     location: statement_location,
                  });
               }
               Some(&Token::Semicolon) => {
                  let sc = l.next().unwrap();
                  let statement_location = merge_locations(expressions[e].location, sc.source_info);
                  statements.push(StatementNode {
                     statement: Statement::Expression(e),
                     location: statement_location,
                  });
               }
               Some(x) => {
                  rolandc_error!(
                     err_manager,
                     l.peek_source().unwrap(),
                     "While parsing statement - unexpected token '{}'; was expecting a semicolon or assignment operator",
                     x.for_parse_err()
                  );
                  return Err(());
               }
               None => {
                  rolandc_error_no_loc!(
                     err_manager,
                     "While parsing statement - unexpected EOF; was expecting a semicolon or assignment operator",
                  );
                  return Err(());
               }
            }
         }
         Some(x) => {
            rolandc_error!(
               err_manager,
               l.peek_source().unwrap(),
               "While parsing block - unexpected token '{}'; was expecting a statement",
               x.for_parse_err()
            );
            return Err(());
         }
         None => {
            rolandc_error_no_loc!(
               err_manager,
               "While parsing block - unexpected EOF; was expecting a statement or a }}"
            );
            return Err(());
         }
      }
   }
   let close_brace = l.next().unwrap();
   Ok(BlockNode {
      statements,
      location: merge_locations(open_brace.source_info, close_brace.source_info),
   })
}

fn parse_if_else_statement(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   expressions: &mut ExpressionPool,
   interner: &Interner,
) -> Result<StatementNode, ()> {
   let if_token = l.next().unwrap();
   let e = parse_expression(l, err_manager, true, expressions, interner)?;
   let if_block = parse_block(l, err_manager, expressions, interner)?;
   let else_statement = match (l.peek_token(), l.double_peek_token()) {
      (Some(&Token::KeywordElse), Some(&Token::KeywordIf)) => {
         let _ = l.next();
         parse_if_else_statement(l, err_manager, expressions, interner)?
      }
      (Some(&Token::KeywordElse), _) => {
         let else_token = l.next().unwrap();
         StatementNode {
            statement: Statement::Block(parse_block(l, err_manager, expressions, interner)?),
            location: else_token.source_info,
         }
      }
      _ => StatementNode {
         statement: Statement::Block(BlockNode {
            statements: vec![],
            location: if_block.location,
         }),
         location: if_token.source_info,
      },
   };
   let combined_location = merge_locations(if_token.source_info, else_statement.location);
   Ok(StatementNode {
      statement: Statement::IfElse(e, if_block, Box::new(else_statement)),
      location: combined_location,
   })
}

fn parse_parameters(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   interner: &Interner,
) -> Result<Vec<ParameterNode>, ()> {
   let mut parameters = vec![];

   loop {
      match l.peek_token() {
         Some(Token::Identifier(_) | Token::KeywordNamed) => {
            let named = if l.peek_token() == Some(&Token::KeywordNamed) {
               let _ = l.next();
               true
            } else {
               false
            };
            let id = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
            expect(l, err_manager, &Token::Colon)?;
            let e_type = parse_type(l, err_manager, interner)?.e_type;
            parameters.push(ParameterNode {
               name: extract_identifier(id.token),
               p_type: e_type,
               named,
            });
            if l.peek_token() == Some(&Token::CloseParen) {
               break;
            }
            expect(l, err_manager, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         Some(x) => {
            rolandc_error!(
               err_manager,
               l.peek_source().unwrap(),
               "While parsing parameters - unexpected token '{}'; was expecting an identifier or a )",
               x.for_parse_err()
            );
            return Err(());
         }
         None => {
            rolandc_error_no_loc!(
               err_manager,
               "While parsing parameters - unexpected EOF; was expecting an identifier or a )",
            );
            return Err(());
         }
      }
   }

   Ok(parameters)
}

fn parse_generic_arguments(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   interner: &Interner,
) -> Result<Vec<GenericArgumentNode>, ()> {
   let mut generic_arguments = vec![];

   while let Some(Token::Dollar) = l.peek_token() {
      let _ = l.next();
      let gtype = parse_type(l, err_manager, interner)?.e_type;
      generic_arguments.push(GenericArgumentNode { gtype });
   }

   Ok(generic_arguments)
}

fn parse_arguments(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   expressions: &mut ExpressionPool,
   interner: &Interner,
) -> Result<Vec<ArgumentNode>, ()> {
   let mut arguments = vec![];

   loop {
      match l.peek_token() {
         Some(
            Token::Identifier(_)
            | Token::BoolLiteral(_)
            | Token::StringLiteral(_)
            | Token::IntLiteral(_)
            | Token::FloatLiteral(_)
            | Token::OpenParen
            | Token::OpenSquareBracket
            | Token::Amp
            | Token::Exclam
            | Token::MultiplyDeref
            | Token::Minus,
         ) => {
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
            let expr = parse_expression(l, err_manager, false, expressions, interner)?;
            arguments.push(ArgumentNode { name, expr });
            let next_discrim = l.peek_token().map(discriminant);
            if next_discrim == Some(discriminant(&Token::CloseParen)) {
               break;
            }
            expect(l, err_manager, &Token::Comma)?;
         }
         Some(Token::CloseParen) => {
            break;
         }
         Some(x) => {
            rolandc_error!(
               err_manager,
               l.peek_source().unwrap(),
               "While parsing arguments - unexpected token '{}'; was expecting an expression or a )",
               x.for_parse_err()
            );
            return Err(());
         }
         None => {
            rolandc_error_no_loc!(
               err_manager,
               "While parsing arguments - unexpected EOF; was expecting an expression or a )",
            );
            return Err(());
         }
      }
   }

   Ok(arguments)
}

fn parse_expression(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   if_head: bool,
   expressions: &mut ExpressionPool,
   interner: &Interner,
) -> Result<ExpressionId, ()> {
   let exp = pratt(l, err_manager, 0, if_head, expressions, interner)?;
   Ok(exp)
}

fn parse_type(l: &mut Lexer, err_manager: &mut ErrorManager, interner: &Interner) -> Result<ExpressionTypeNode, ()> {
   let mut ptr_count: usize = 0;
   let loc_start = l.peek_source();
   while let Some(&Token::Amp) = l.peek_token() {
      ptr_count += 1;
      let _ = l.next();
   }

   let (loc_end, value_type) = match l.peek_token() {
      Some(Token::OpenSquareBracket) => {
         let _ = l.next();
         let a_inner_type = parse_type(l, err_manager, interner)?;
         expect(l, err_manager, &Token::Semicolon)?;
         let length = expect(l, err_manager, &Token::IntLiteral(0))?;
         let t_close_token = expect(l, err_manager, &Token::CloseSquareBracket)?;
         (
            t_close_token.source_info,
            ValueType::Array(Box::new(a_inner_type.e_type), extract_int_literal(length.token)),
         )
      }
      Some(Token::OpenParen) => {
         let _ = l.next();
         let close_token = expect(l, err_manager, &Token::CloseParen)?;
         (close_token.source_info, ValueType::Unit)
      }
      _ => {
         let type_token = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
         let type_s = extract_identifier(type_token.token);
         (
            type_token.source_info,
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
            },
         )
      }
   };

   if ptr_count > 0 {
      Ok(ExpressionTypeNode {
         e_type: ExpressionType::Pointer(ptr_count, value_type),
         location: merge_locations(loc_start.unwrap(), loc_end),
      })
   } else {
      Ok(ExpressionTypeNode {
         e_type: ExpressionType::Value(value_type),
         location: merge_locations(loc_start.unwrap(), loc_end),
      })
   }
}

fn pratt(
   l: &mut Lexer,
   err_manager: &mut ErrorManager,
   min_bp: u8,
   if_head: bool,
   expressions: &mut ExpressionPool,
   interner: &Interner,
) -> Result<ExpressionId, ()> {
   let expr_begin_token = l.next();
   let expr_begin_source = expr_begin_token.as_ref().map(|x| x.source_info);
   let mut lhs = match expr_begin_token.map(|x| x.token) {
      Some(Token::BoolLiteral(x)) => wrap(Expression::BoolLiteral(x), expr_begin_source.unwrap(), expressions),
      Some(Token::IntLiteral(x)) => wrap(Expression::IntLiteral(x), expr_begin_source.unwrap(), expressions),
      Some(Token::FloatLiteral(x)) => wrap(Expression::FloatLiteral(x), expr_begin_source.unwrap(), expressions),
      Some(Token::StringLiteral(x)) => wrap(Expression::StringLiteral(x), expr_begin_source.unwrap(), expressions),
      Some(Token::Identifier(s)) => {
         if l.peek_token() == Some(&Token::Dollar) {
            let generic_args = parse_generic_arguments(l, err_manager, interner)?;
            expect(l, err_manager, &Token::OpenParen)?;
            let args = parse_arguments(l, err_manager, expressions, interner)?;
            let close_token = expect(l, err_manager, &Token::CloseParen)?;
            let combined_location = merge_locations(expr_begin_source.unwrap(), close_token.source_info);
            wrap(
               Expression::ProcedureCall {
                  proc_name: s,
                  generic_args: generic_args.into_boxed_slice(),
                  args: args.into_boxed_slice(),
               },
               combined_location,
               expressions,
            )
         } else if l.peek_token() == Some(&Token::OpenParen) {
            let _ = l.next();
            let args = parse_arguments(l, err_manager, expressions, interner)?;
            let close_token = expect(l, err_manager, &Token::CloseParen)?;
            let combined_location = merge_locations(expr_begin_source.unwrap(), close_token.source_info);
            wrap(
               Expression::ProcedureCall {
                  proc_name: s,
                  generic_args: vec![].into_boxed_slice(),
                  args: args.into_boxed_slice(),
               },
               combined_location,
               expressions,
            )
         } else if l.peek_token() == Some(&Token::DoubleColon) {
            let _ = l.next();
            let variant = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
            let variant_identifier = extract_identifier(variant.token);
            let combined_location = merge_locations(expr_begin_source.unwrap(), variant.source_info);
            wrap(
               Expression::EnumLiteral(s, variant_identifier),
               combined_location,
               expressions,
            )
         } else if !if_head && l.peek_token() == Some(&Token::OpenBrace) {
            let _ = l.next();
            let mut fields = vec![];
            loop {
               if let Some(&Token::CloseBrace) = l.peek_token() {
                  break;
               }
               let identifier = extract_identifier(expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?.token);
               let _ = expect(l, err_manager, &Token::Colon)?;
               let val = parse_expression(l, err_manager, false, expressions, interner)?;
               fields.push((identifier, val));
               if let Some(&Token::CloseBrace) = l.peek_token() {
                  break;
               } else if let Some(&Token::Identifier(x)) = l.peek_token().as_ref() {
                  let struct_str = interner.lookup(s);
                  let identifier_str = interner.lookup(*x);
                  rolandc_error!(
                     err_manager,
                     l.peek_source().unwrap(),
                     "While parsing instantiation of struct `{}`, encountered an unexpected identifier `{}`. Hint: Are you missing a comma?",
                     struct_str,
                     identifier_str,
                  );
                  return Result::Err(());
               };
               expect(l, err_manager, &Token::Comma)?;
            }
            let closing_brace = l.next().unwrap();
            let combined_location = merge_locations(expr_begin_source.unwrap(), closing_brace.source_info);
            wrap(Expression::StructLiteral(s, fields), combined_location, expressions)
         } else {
            wrap(Expression::Variable(s), expr_begin_source.unwrap(), expressions)
         }
      }
      Some(Token::OpenParen) => {
         if let Some(&Token::CloseParen) = l.peek_token() {
            let end_token = l.next().unwrap();
            let combined_location = merge_locations(expr_begin_source.unwrap(), end_token.source_info);
            wrap(Expression::UnitLiteral, combined_location, expressions)
         } else {
            let new_lhs = pratt(l, err_manager, 0, false, expressions, interner)?;
            expect(l, err_manager, &Token::CloseParen)?;
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
            es.push(parse_expression(l, err_manager, false, expressions, interner)?);
            if let Some(Token::CloseSquareBracket) = l.peek_token() {
               break;
            }
            expect(l, err_manager, &Token::Comma)?;
         }
         let closing_token = l.next().unwrap(); // ]
         let combined_location = merge_locations(expr_begin_source.unwrap(), closing_token.source_info);
         wrap(
            Expression::ArrayLiteral(es.into_boxed_slice()),
            combined_location,
            expressions,
         )
      }
      Some(x @ Token::Minus) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_manager, r_bp, if_head, expressions, interner)?;
         let combined_location = merge_locations(expr_begin_source.unwrap(), begin_location.unwrap());
         wrap(
            Expression::UnaryOperator(UnOp::Negate, rhs),
            combined_location,
            expressions,
         )
      }
      Some(x @ Token::Exclam) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_manager, r_bp, if_head, expressions, interner)?;
         let combined_location = merge_locations(expr_begin_source.unwrap(), begin_location.unwrap());
         wrap(
            Expression::UnaryOperator(UnOp::Complement, rhs),
            combined_location,
            expressions,
         )
      }
      Some(x @ Token::Amp) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_manager, r_bp, if_head, expressions, interner)?;
         let combined_location = merge_locations(expr_begin_source.unwrap(), begin_location.unwrap());
         wrap(
            Expression::UnaryOperator(UnOp::AddressOf, rhs),
            combined_location,
            expressions,
         )
      }
      Some(x @ Token::MultiplyDeref) => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, err_manager, r_bp, if_head, expressions, interner)?;
         let combined_location = merge_locations(expr_begin_source.unwrap(), begin_location.unwrap());
         wrap(
            Expression::UnaryOperator(UnOp::Dereference, rhs),
            combined_location,
            expressions,
         )
      }
      x => {
         if let Some(si) = expr_begin_source {
            rolandc_error!(
               err_manager,
               si,
               "While parsing expression - unexpected token '{}'; was expecting a literal, call, variable, or prefix operator",
               x.unwrap().for_parse_err(),
            );
         } else {
            rolandc_error_no_loc!(
               err_manager,
               "While parsing expression - unexpected EOF; was expecting a literal, call, variable, or prefix operator",
            );
         }
         return Err(());
      }
   };

   loop {
      let op: &Token = match l.peek_token() {
         Some(
            x @ &(Token::Plus
            | Token::Minus
            | Token::MultiplyDeref
            | Token::Divide
            | Token::Remainder
            | Token::LessThan
            | Token::LessThanOrEqualTo
            | Token::GreaterThan
            | Token::GreaterThanOrEqualTo
            | Token::Equality
            | Token::Amp
            | Token::KeywordAnd
            | Token::KeywordOr
            | Token::Pipe
            | Token::Caret
            | Token::NotEquality
            | Token::KeywordExtend
            | Token::KeywordTruncate
            | Token::KeywordTransmute
            | Token::OpenSquareBracket
            | Token::ShiftLeft
            | Token::ShiftRight),
         ) => x,
         Some(&Token::Period) => {
            let mut fields = vec![];
            let mut last_location;
            loop {
               let _ = l.next();
               let ident_token = expect(l, err_manager, &Token::Identifier(DUMMY_STR_TOKEN))?;
               last_location = ident_token.source_info;
               fields.push(extract_identifier(ident_token.token));
               if l.peek_token() != Some(&Token::Period) {
                  break;
               }
            }
            let combined_location = merge_locations(expr_begin_source.unwrap(), last_location);
            lhs = wrap(Expression::FieldAccess(fields, lhs), combined_location, expressions);
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
               let inner = parse_expression(l, err_manager, false, expressions, interner)?;
               let close_token = expect(l, err_manager, &Token::CloseSquareBracket)?;
               let combined_location = merge_locations(expr_begin_source.unwrap(), close_token.source_info);
               wrap(
                  Expression::ArrayIndex {
                     array: lhs,
                     index: inner,
                  },
                  combined_location,
                  expressions,
               )
            }
            Token::KeywordExtend => {
               let a_type = parse_type(l, err_manager, interner)?;
               let combined_location = merge_locations(expr_begin_source.unwrap(), a_type.location);
               wrap(Expression::Extend(a_type.e_type, lhs), combined_location, expressions)
            }
            Token::KeywordTruncate => {
               let a_type = parse_type(l, err_manager, interner)?;
               let combined_location = merge_locations(expr_begin_source.unwrap(), a_type.location);
               wrap(Expression::Truncate(a_type.e_type, lhs), combined_location, expressions)
            }
            Token::KeywordTransmute => {
               let a_type = parse_type(l, err_manager, interner)?;
               let combined_location = merge_locations(expr_begin_source.unwrap(), a_type.location);
               wrap(
                  Expression::Transmute(a_type.e_type, lhs),
                  combined_location,
                  expressions,
               )
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
      let rhs = pratt(l, err_manager, r_b, if_head, expressions, interner)?;

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

      let combined_location = merge_locations(expressions[lhs].location, expressions[rhs].location);
      lhs = wrap(
         Expression::BinaryOperator {
            operator: bin_op,
            lhs,
            rhs,
         },
         combined_location,
         expressions,
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

fn wrap(expression: Expression, source_info: SourceInfo, expressions: &mut ExpressionPool) -> ExpressionId {
   expressions.push(ExpressionNode {
      expression,
      exp_type: None,
      location: source_info,
   })
}
