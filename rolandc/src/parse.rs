use super::lex::{SourceToken, Token};
use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId, DUMMY_STR_TOKEN};
use crate::lex::Lexer;
use crate::semantic_analysis::{EnumInfo, GlobalInfo, ProcedureInfo, StructInfo};
use crate::size_info::SizeInfo;
use crate::source_info::SourceInfo;
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

fn expect(l: &mut Lexer, parse_context: &mut ParseContext, token: Token) -> Result<SourceToken, ()> {
   let lex_token = l.next();
   if discriminant(&lex_token.token) == discriminant(&token) {
      Ok(lex_token)
   } else {
      rolandc_error!(
         &mut parse_context.err_manager,
         lex_token.source_info,
         "Encountered {} when expecting {}",
         lex_token.token.for_parse_err(),
         token.for_parse_err()
      );
      Err(())
   }
}

#[derive(Clone)]
pub struct ProcedureDefinition {
   pub name: StrId,
   pub generic_parameters: Vec<IdentifierNode>,
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
   pub location: SourceInfo,
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
   pub variants: Vec<IdentifierNode>,
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CastType {
   Extend,
   Truncate,
   Transmute,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
   ProcedureCall {
      proc_name: IdentifierNode,
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
   IntLiteral {
      val: u64,
      synthetic: bool,
   },
   FloatLiteral(f64),
   UnitLiteral,
   Variable(IdentifierNode),
   BinaryOperator {
      operator: BinOp,
      lhs: ExpressionId,
      rhs: ExpressionId,
   },
   UnaryOperator(UnOp, ExpressionId),
   StructLiteral(IdentifierNode, Box<[(StrId, ExpressionId)]>),
   FieldAccess(Vec<StrId>, ExpressionId),
   Cast {
      cast_type: CastType,
      target_type: ExpressionType,
      expr: ExpressionId,
   },
   EnumLiteral(IdentifierNode, IdentifierNode),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgumentNode {
   pub name: Option<StrId>,
   pub expr: ExpressionId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericArgumentNode {
   pub gtype: ExpressionType,
}

impl Expression {
   #[must_use]
   pub fn is_lvalue(&self, expressions: &ExpressionPool, global_info: &IndexMap<StrId, GlobalInfo>) -> bool {
      match self {
         Expression::Variable(x) => global_info.get(&x.identifier).map_or(true, |x| !x.is_const),
         Expression::ArrayIndex { array, .. } => expressions[*array].expression.is_lvalue(expressions, global_info),
         Expression::UnaryOperator(UnOp::Dereference, _) => true,
         Expression::FieldAccess(_, lhs) => expressions[*lhs].expression.is_lvalue(expressions, global_info),
         _ => false,
      }
   }

   // After constants are lowered, we don't need to care about constants and pass a bulky data structure around
   #[must_use]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

   pub parsed_types: Vec<ExpressionTypeNode>, // (only read by the language server)

   // These fields are populated during semantic analysis
   pub literals: IndexSet<StrId>,
   pub enum_info: IndexMap<StrId, EnumInfo>,
   pub struct_info: IndexMap<StrId, StructInfo>,
   pub global_info: IndexMap<StrId, GlobalInfo>,
   pub procedure_info: IndexMap<StrId, ProcedureInfo>,
   pub struct_size_info: HashMap<StrId, SizeInfo>,
   pub source_to_definition: IndexMap<SourceInfo, SourceInfo>,
}

impl Program {
   #[must_use]
   pub fn new() -> Program {
      Program {
         enums: Vec::new(),
         external_procedures: Vec::new(),
         procedures: Vec::new(),
         structs: Vec::new(),
         consts: Vec::new(),
         statics: Vec::new(),
         parsed_types: Vec::new(),
         literals: IndexSet::new(),
         enum_info: IndexMap::new(),
         struct_info: IndexMap::new(),
         global_info: IndexMap::new(),
         procedure_info: IndexMap::new(),
         struct_size_info: HashMap::new(),
         source_to_definition: IndexMap::new(),
      }
   }
}

fn token_starts_expression(token: Token) -> bool {
   matches!(
      token,
      Token::BoolLiteral(_)
         | Token::StringLiteral(_)
         | Token::IntLiteral(_)
         | Token::FloatLiteral(_)
         | Token::OpenParen
         | Token::OpenSquareBracket
         | Token::Exclam
         | Token::Amp
         | Token::Identifier(_)
         | Token::Minus
   )
}

struct ParseContext<'a> {
   err_manager: &'a mut ErrorManager,
   interner: &'a Interner,
   parsed_types: Vec<ExpressionTypeNode>,
}

pub fn astify(
   mut lexer: Lexer,
   err_manager: &mut ErrorManager,
   interner: &Interner,
   expressions: &mut ExpressionPool,
) -> Result<(Vec<ImportNode>, Program), ()> {
   let mut parse_context = ParseContext {
      err_manager,
      interner,
      parsed_types: Vec::new(),
   };

   let mut external_procedures = vec![];
   let mut procedures = vec![];
   let mut structs = vec![];
   let mut enums = vec![];
   let mut consts = vec![];
   let mut statics = vec![];
   let mut imports = vec![];

   loop {
      let peeked_token = lexer.peek_token();
      match peeked_token {
         Token::KeywordExtern => {
            let extern_kw = lexer.next();
            expect(&mut lexer, &mut parse_context, Token::KeywordProcedureDef)?;
            let p = parse_external_procedure(
               &mut lexer,
               &mut parse_context,
               extern_kw.source_info,
               ProcImplSource::External,
            )?;
            external_procedures.push(p);
         }
         Token::KeywordBuiltin => {
            let builtin_kw = lexer.next();
            expect(&mut lexer, &mut parse_context, Token::KeywordProcedureDef)?;
            let p = parse_external_procedure(
               &mut lexer,
               &mut parse_context,
               builtin_kw.source_info,
               ProcImplSource::Builtin,
            )?;
            external_procedures.push(p);
         }
         Token::KeywordProcedureDef => {
            let def = lexer.next();
            let p = parse_procedure(&mut lexer, &mut parse_context, def.source_info, expressions)?;
            procedures.push(p);
         }
         Token::KeywordImport => {
            let kw = lexer.next();
            let import_token = expect(&mut lexer, &mut parse_context, Token::StringLiteral(DUMMY_STR_TOKEN))?;
            let sc = expect(&mut lexer, &mut parse_context, Token::Semicolon)?;
            imports.push(ImportNode {
               import_path: extract_str_literal(import_token.token),
               location: merge_locations(kw.source_info, sc.source_info),
            });
         }
         Token::KeywordStructDef => {
            let def = lexer.next();
            let s = parse_struct(&mut lexer, &mut parse_context, def.source_info)?;
            structs.push(s);
         }
         Token::KeywordEnumDef => {
            let def = lexer.next();
            let s = parse_enum(&mut lexer, &mut parse_context, def.source_info)?;
            enums.push(s);
         }
         Token::KeywordConst => {
            let a_const = lexer.next();
            let variable_name = parse_identifier(&mut lexer, &mut parse_context)?;
            expect(&mut lexer, &mut parse_context, Token::Colon)?;
            let t_type = parse_type(&mut lexer, &mut parse_context)?;
            expect(&mut lexer, &mut parse_context, Token::Assignment)?;
            let exp = parse_expression(&mut lexer, &mut parse_context, false, expressions)?;
            let end_token = expect(&mut lexer, &mut parse_context, Token::Semicolon)?;
            consts.push(ConstNode {
               name: variable_name,
               const_type: t_type.e_type,
               location: merge_locations(a_const.source_info, end_token.source_info),
               value: exp,
            });
         }
         Token::KeywordStatic => {
            let a_static = lexer.next();
            let variable_name = parse_identifier(&mut lexer, &mut parse_context)?;
            expect(&mut lexer, &mut parse_context, Token::Colon)?;
            let t_type = parse_type(&mut lexer, &mut parse_context)?;
            let exp = if lexer.peek_token() == Token::Assignment {
               let _ = lexer.next();
               Some(parse_expression(&mut lexer, &mut parse_context, false, expressions)?)
            } else {
               None
            };
            let end_token = expect(&mut lexer, &mut parse_context, Token::Semicolon)?;
            statics.push(StaticNode {
               name: variable_name,
               static_type: t_type.e_type,
               location: merge_locations(a_static.source_info, end_token.source_info),
               value: exp,
            });
         }
         Token::Eof => {
            break;
         }
         x => {
            rolandc_error!(
               err_manager,
               lexer.peek_source(),
               "While parsing top level, encountered unexpected {}; was expecting a procedure, const, static, enum, or struct declaration",
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
         parsed_types: parse_context.parsed_types,
         literals: IndexSet::new(),
         struct_info: IndexMap::new(),
         global_info: IndexMap::new(),
         enum_info: IndexMap::new(),
         procedure_info: IndexMap::new(),
         struct_size_info: HashMap::new(),
         source_to_definition: IndexMap::new(),
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

fn extract_int_literal(t: Token) -> u64 {
   match t {
      Token::IntLiteral(v) => v,
      _ => unreachable!(),
   }
}

fn parse_identifier(l: &mut Lexer, parse_context: &mut ParseContext) -> Result<IdentifierNode, ()> {
   let ident = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
   Ok(IdentifierNode {
      identifier: extract_identifier(ident.token),
      location: ident.source_info,
   })
}

fn parse_procedure_definition(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
) -> Result<ProcedureDefinition, ()> {
   let procedure_name = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
   let mut generic_parameters = vec![];
   while l.peek_token() == Token::Dollar {
      let _ = l.next();
      let gtype_definition = parse_identifier(l, parse_context)?;
      generic_parameters.push(gtype_definition);
   }
   expect(l, parse_context, Token::OpenParen)?;
   let parameters = parse_parameters(l, parse_context)?;
   expect(l, parse_context, Token::CloseParen)?;
   let ret_type = if l.peek_token() == Token::Arrow {
      let _ = l.next();
      parse_type(l, parse_context)?.e_type
   } else {
      ExpressionType::Value(ValueType::Unit)
   };
   Ok(ProcedureDefinition {
      name: extract_identifier(procedure_name.token),
      generic_parameters,
      parameters,
      ret_type,
   })
}

fn parse_procedure(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   source_info: SourceInfo,
   expressions: &mut ExpressionPool,
) -> Result<ProcedureNode, ()> {
   let definition = parse_procedure_definition(l, parse_context)?;
   let block = parse_block(l, parse_context, expressions)?;
   let combined_location = merge_locations(source_info, block.location);
   Ok(ProcedureNode {
      definition,
      locals: IndexMap::new(),
      virtual_locals: IndexSet::new(),
      block,
      location: combined_location,
   })
}

fn parse_external_procedure(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   source_info: SourceInfo,
   proc_impl_source: ProcImplSource,
) -> Result<ExternalProcedureNode, ()> {
   let definition = parse_procedure_definition(l, parse_context)?;
   let end_token = expect(l, parse_context, Token::Semicolon)?;
   Ok(ExternalProcedureNode {
      definition,
      location: merge_locations(source_info, end_token.source_info),
      impl_source: proc_impl_source,
   })
}

fn parse_struct(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   source_info: SourceInfo,
) -> Result<StructNode, ()> {
   let struct_name = extract_identifier(expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?.token);
   expect(l, parse_context, Token::OpenBrace)?;
   let mut fields: Vec<(StrId, ExpressionType)> = vec![];
   let close_brace = loop {
      if l.peek_token() == Token::CloseBrace {
         break l.next();
      }
      let identifier = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
      let _ = expect(l, parse_context, Token::Colon)?;
      let f_type = parse_type(l, parse_context)?.e_type;
      fields.push((extract_identifier(identifier.token), f_type));
      if l.peek_token() == Token::CloseBrace {
         break l.next();
      } else if let Token::Identifier(x) = l.peek_token() {
         rolandc_error!(
            &mut parse_context.err_manager,
            l.peek_source(),
            "While parsing definition of struct `{}`, encountered an unexpected identifier `{}`. Hint: Are you missing a comma?",
            parse_context.interner.lookup(struct_name),
            parse_context.interner.lookup(x),
         );
         return Result::Err(());
      }
      expect(l, parse_context, Token::Comma)?;
   };
   Ok(StructNode {
      name: struct_name,
      fields,
      location: merge_locations(source_info, close_brace.source_info),
   })
}

fn parse_enum(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   source_info: SourceInfo,
) -> Result<EnumNode, ()> {
   let enum_name = extract_identifier(expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?.token);
   expect(l, parse_context, Token::OpenBrace)?;
   let mut variants = vec![];
   let close_brace = loop {
      if l.peek_token() == Token::CloseBrace {
         break l.next();
      }
      variants.push(parse_identifier(l, parse_context)?);
      if l.peek_token() == Token::CloseBrace {
         break l.next();
      } else if let Token::Identifier(x) = l.peek_token() {
         rolandc_error!(
            &mut parse_context.err_manager,
            l.peek_source(),
            "While parsing definition of enum `{}`, encountered an unexpected identifier `{}`. Hint: Are you missing a comma?",
            parse_context.interner.lookup(enum_name),
            parse_context.interner.lookup(x),
         );
         return Result::Err(());
      }

      expect(l, parse_context, Token::Comma)?;
   };
   Ok(EnumNode {
      name: enum_name,
      variants,
      location: merge_locations(source_info, close_brace.source_info),
   })
}

fn parse_block(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   expressions: &mut ExpressionPool,
) -> Result<BlockNode, ()> {
   let open_brace = expect(l, parse_context, Token::OpenBrace)?;

   let mut statements: Vec<StatementNode> = vec![];

   let close_brace = loop {
      match l.peek_token() {
         Token::OpenBrace => {
            let source = l.peek_source();
            let new_block = parse_block(l, parse_context, expressions)?;
            statements.push(StatementNode {
               statement: Statement::Block(new_block),
               location: source,
            });
         }
         Token::CloseBrace => {
            break l.next();
         }
         Token::KeywordContinue => {
            let continue_token = l.next();
            let sc = expect(l, parse_context, Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::Continue,
               location: merge_locations(continue_token.source_info, sc.source_info),
            });
         }
         Token::KeywordBreak => {
            let break_token = l.next();
            let sc = expect(l, parse_context, Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::Break,
               location: merge_locations(break_token.source_info, sc.source_info),
            });
         }
         Token::KeywordFor => {
            let for_token = l.next();
            let variable_name = parse_identifier(l, parse_context)?;
            let _ = expect(l, parse_context, Token::KeywordIn)?;
            let start_en = parse_expression(l, parse_context, true, expressions)?;
            let _ = expect(l, parse_context, Token::DoublePeriod)?;
            let inclusive = if l.peek_token() == Token::Assignment {
               let _ = l.next();
               true
            } else {
               false
            };
            let end_en = parse_expression(l, parse_context, true, expressions)?;
            let new_block = parse_block(l, parse_context, expressions)?;
            statements.push(StatementNode {
               statement: Statement::For(variable_name, start_en, end_en, new_block, inclusive),
               location: for_token.source_info,
            });
         }
         Token::KeywordLoop => {
            let loop_token = l.next();
            let new_block = parse_block(l, parse_context, expressions)?;
            statements.push(StatementNode {
               statement: Statement::Loop(new_block),
               location: loop_token.source_info,
            });
         }
         Token::KeywordReturn => {
            let return_token = l.next();
            let e = if l.peek_token() == Token::Semicolon {
               wrap(Expression::UnitLiteral, return_token.source_info, expressions)
            } else {
               parse_expression(l, parse_context, false, expressions)?
            };
            let sc = expect(l, parse_context, Token::Semicolon)?;
            statements.push(StatementNode {
               statement: Statement::Return(e),
               location: merge_locations(return_token.source_info, sc.source_info),
            });
         }
         Token::KeywordLet => {
            let mut declared_type = None;
            let let_token = l.next();
            let variable_name = parse_identifier(l, parse_context)?;
            if l.peek_token() == Token::Colon {
               let _ = l.next();
               declared_type = Some(parse_type(l, parse_context)?);
            }
            expect(l, parse_context, Token::Assignment)?;
            let e = parse_expression(l, parse_context, false, expressions)?;
            let sc = expect(l, parse_context, Token::Semicolon)?;
            let statement_location = merge_locations(let_token.source_info, sc.source_info);
            statements.push(StatementNode {
               statement: Statement::VariableDeclaration(variable_name, e, declared_type.map(|x| x.e_type)),
               location: statement_location,
            });
         }
         Token::KeywordIf => {
            let s = parse_if_else_statement(l, parse_context, expressions)?;
            statements.push(s);
         }
         x if token_starts_expression(x) => {
            let e = parse_expression(l, parse_context, false, expressions)?;
            match l.peek_token() {
               Token::Assignment => {
                  let _ = l.next();
                  let re = parse_expression(l, parse_context, false, expressions)?;
                  let sc = expect(l, parse_context, Token::Semicolon)?;
                  let statement_location = merge_locations(expressions[e].location, sc.source_info);
                  statements.push(StatementNode {
                     statement: Statement::Assignment(e, re),
                     location: statement_location,
                  });
               }
               Token::Semicolon => {
                  let sc = l.next();
                  let statement_location = merge_locations(expressions[e].location, sc.source_info);
                  statements.push(StatementNode {
                     statement: Statement::Expression(e),
                     location: statement_location,
                  });
               }
               x => {
                  rolandc_error!(
                     &mut parse_context.err_manager,
                     l.peek_source(),
                     "While parsing statement, encountered unexpected {}; was expecting a semicolon or assignment operator",
                     x.for_parse_err()
                  );
                  return Err(());
               }
            }
         }
         x => {
            rolandc_error!(
               &mut parse_context.err_manager,
               l.peek_source(),
               "While parsing block, encountered unexpected {}; was expecting a statement",
               x.for_parse_err()
            );
            return Err(());
         }
      }
   };
   Ok(BlockNode {
      statements,
      location: merge_locations(open_brace.source_info, close_brace.source_info),
   })
}

fn parse_if_else_statement(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   expressions: &mut ExpressionPool,
) -> Result<StatementNode, ()> {
   let if_token = l.next();
   let e = parse_expression(l, parse_context, true, expressions)?;
   let if_block = parse_block(l, parse_context, expressions)?;
   let else_statement = match (l.peek_token(), l.double_peek_token()) {
      (Token::KeywordElse, Token::KeywordIf) => {
         let _ = l.next();
         parse_if_else_statement(l, parse_context, expressions)?
      }
      (Token::KeywordElse, _) => {
         let else_token = l.next();
         StatementNode {
            statement: Statement::Block(parse_block(l, parse_context, expressions)?),
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
   parse_context: &mut ParseContext,
) -> Result<Vec<ParameterNode>, ()> {
   let mut parameters = vec![];

   loop {
      match l.peek_token() {
         Token::Identifier(_) | Token::KeywordNamed => {
            let named = if l.peek_token() == Token::KeywordNamed {
               let _ = l.next();
               true
            } else {
               false
            };
            let id = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
            expect(l, parse_context, Token::Colon)?;
            let e_type = parse_type(l, parse_context)?.e_type;
            parameters.push(ParameterNode {
               name: extract_identifier(id.token),
               location: id.source_info,
               p_type: e_type,
               named,
            });
            if l.peek_token() == Token::CloseParen {
               break;
            }
            expect(l, parse_context, Token::Comma)?;
         }
         Token::CloseParen => {
            break;
         }
         x => {
            rolandc_error!(
               &mut parse_context.err_manager,
               l.peek_source(),
               "While parsing parameters, encountered unexpected {}; was expecting an identifier or a )",
               x.for_parse_err()
            );
            return Err(());
         }
      }
   }

   Ok(parameters)
}

fn parse_generic_arguments(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
) -> Result<Vec<GenericArgumentNode>, ()> {
   let mut generic_arguments = vec![];

   while l.peek_token() == Token::Dollar {
      let _ = l.next();
      let gtype = parse_type(l, parse_context)?.e_type;
      generic_arguments.push(GenericArgumentNode { gtype });
   }

   Ok(generic_arguments)
}

fn parse_arguments(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   expressions: &mut ExpressionPool,
) -> Result<Vec<ArgumentNode>, ()> {
   let mut arguments = vec![];

   loop {
      match l.peek_token() {
         x if token_starts_expression(x) => {
            let name: Option<StrId> = if let Token::Identifier(x) = l.peek_token() {
               if l.double_peek_token() == Token::Colon {
                  let _ = l.next();
                  let _ = l.next();
                  Some(x)
               } else {
                  None
               }
            } else {
               None
            };
            let expr = parse_expression(l, parse_context, false, expressions)?;
            arguments.push(ArgumentNode { name, expr });
            if l.peek_token() == Token::CloseParen {
               break;
            }
            expect(l, parse_context, Token::Comma)?;
         }
         Token::CloseParen => {
            break;
         }
         x => {
            rolandc_error!(
               &mut parse_context.err_manager,
               l.peek_source(),
               "While parsing arguments, encountered unexpected {}; was expecting an expression or a )",
               x.for_parse_err()
            );
            return Err(());
         }
      }
   }

   Ok(arguments)
}

fn parse_expression(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   if_head: bool,
   expressions: &mut ExpressionPool,
) -> Result<ExpressionId, ()> {
   let exp = pratt(l, parse_context, 0, if_head, expressions)?;
   Ok(exp)
}

fn parse_type(l: &mut Lexer, parse_context: &mut ParseContext) -> Result<ExpressionTypeNode, ()> {
   let mut ptr_count: usize = 0;
   let loc_start = l.peek_source();
   while l.peek_token() == Token::Amp {
      ptr_count += 1;
      let _ = l.next();
   }

   let (loc_end, value_type) = match l.peek_token() {
      Token::OpenSquareBracket => {
         let _ = l.next();
         let a_inner_type = parse_type(l, parse_context)?;
         expect(l, parse_context, Token::Semicolon)?;
         let length = expect(l, parse_context, Token::IntLiteral(0))?;
         let t_close_token = expect(l, parse_context, Token::CloseSquareBracket)?;

         let arr_len_literal = extract_int_literal(length.token);

         if let Ok(valid_arr_len) = arr_len_literal.try_into() {
            (
               t_close_token.source_info,
               ValueType::Array(Box::new(a_inner_type.e_type), valid_arr_len),
            )
         } else {
            rolandc_error!(
               &mut parse_context.err_manager,
               length.source_info,
               "While parsing array type, encountered an overly big integer {}. The maximum length of an array is 4294967295.",
               arr_len_literal
            );
            return Err(());
         }
      }
      Token::OpenParen => {
         let _ = l.next();
         let close_token = expect(l, parse_context, Token::CloseParen)?;
         (close_token.source_info, ValueType::Unit)
      }
      _ => {
         let type_token = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
         let type_s = extract_identifier(type_token.token);
         (
            type_token.source_info,
            match parse_context.interner.lookup(type_s) {
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

   let etn = if ptr_count > 0 {
      ExpressionTypeNode {
         e_type: ExpressionType::Pointer(ptr_count, value_type),
         location: merge_locations(loc_start, loc_end),
      }
   } else {
      ExpressionTypeNode {
         e_type: ExpressionType::Value(value_type),
         location: merge_locations(loc_start, loc_end),
      }
   };

   parse_context.parsed_types.push(etn.clone());

   Ok(etn)
}

fn pratt(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   min_bp: u8,
   if_head: bool,
   expressions: &mut ExpressionPool,
) -> Result<ExpressionId, ()> {
   let expr_begin_token = l.next();
   let mut lhs = match expr_begin_token.token {
      Token::BoolLiteral(x) => wrap(Expression::BoolLiteral(x), expr_begin_token.source_info, expressions),
      Token::IntLiteral(x) => wrap(
         Expression::IntLiteral {
            val: x,
            synthetic: false,
         },
         expr_begin_token.source_info,
         expressions,
      ),
      Token::FloatLiteral(x) => wrap(Expression::FloatLiteral(x), expr_begin_token.source_info, expressions),
      Token::StringLiteral(x) => wrap(Expression::StringLiteral(x), expr_begin_token.source_info, expressions),
      Token::Identifier(s) => {
         if l.peek_token() == Token::Dollar {
            let generic_args = parse_generic_arguments(l, parse_context)?;
            expect(l, parse_context, Token::OpenParen)?;
            let args = parse_arguments(l, parse_context, expressions)?;
            let close_token = expect(l, parse_context, Token::CloseParen)?;
            let combined_location = merge_locations(expr_begin_token.source_info, close_token.source_info);
            wrap(
               Expression::ProcedureCall {
                  proc_name: IdentifierNode {
                     identifier: s,
                     location: expr_begin_token.source_info,
                  },
                  generic_args: generic_args.into_boxed_slice(),
                  args: args.into_boxed_slice(),
               },
               combined_location,
               expressions,
            )
         } else if l.peek_token() == Token::OpenParen {
            let _ = l.next();
            let args = parse_arguments(l, parse_context, expressions)?;
            let close_token = expect(l, parse_context, Token::CloseParen)?;
            let combined_location = merge_locations(expr_begin_token.source_info, close_token.source_info);
            wrap(
               Expression::ProcedureCall {
                  proc_name: IdentifierNode {
                     identifier: s,
                     location: expr_begin_token.source_info,
                  },
                  generic_args: vec![].into_boxed_slice(),
                  args: args.into_boxed_slice(),
               },
               combined_location,
               expressions,
            )
         } else if l.peek_token() == Token::DoubleColon {
            let _ = l.next();
            let variant = parse_identifier(l, parse_context)?;
            let combined_location = merge_locations(expr_begin_token.source_info, variant.location);
            wrap(
               Expression::EnumLiteral(
                  IdentifierNode {
                     identifier: s,
                     location: expr_begin_token.source_info,
                  },
                  variant,
               ),
               combined_location,
               expressions,
            )
         } else if !if_head && l.peek_token() == Token::OpenBrace {
            let _ = l.next();
            let mut fields = vec![];
            let close_brace = loop {
               if l.peek_token() == Token::CloseBrace {
                  break l.next();
               }
               let identifier = extract_identifier(expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?.token);
               let _ = expect(l, parse_context, Token::Colon)?;
               let val = parse_expression(l, parse_context, false, expressions)?;
               fields.push((identifier, val));
               if l.peek_token() == Token::CloseBrace {
                  break l.next();
               } else if let Token::Identifier(x) = l.peek_token() {
                  let struct_str = parse_context.interner.lookup(s);
                  let identifier_str = parse_context.interner.lookup(x);
                  rolandc_error!(
                     &mut parse_context.err_manager,
                     l.peek_source(),
                     "While parsing instantiation of struct `{}`, encountered an unexpected identifier `{}`. Hint: Are you missing a comma?",
                     struct_str,
                     identifier_str,
                  );
                  return Result::Err(());
               };
               expect(l, parse_context, Token::Comma)?;
            };
            let combined_location = merge_locations(expr_begin_token.source_info, close_brace.source_info);
            wrap(
               Expression::StructLiteral(
                  IdentifierNode {
                     identifier: s,
                     location: expr_begin_token.source_info,
                  },
                  fields.into_boxed_slice(),
               ),
               combined_location,
               expressions,
            )
         } else {
            wrap(
               Expression::Variable(IdentifierNode {
                  identifier: s,
                  location: expr_begin_token.source_info,
               }),
               expr_begin_token.source_info,
               expressions,
            )
         }
      }
      Token::OpenParen => {
         if l.peek_token() == Token::CloseParen {
            let end_token = l.next();
            let combined_location = merge_locations(expr_begin_token.source_info, end_token.source_info);
            wrap(Expression::UnitLiteral, combined_location, expressions)
         } else {
            let new_lhs = pratt(l, parse_context, 0, false, expressions)?;
            expect(l, parse_context, Token::CloseParen)?;
            new_lhs
         }
      }
      Token::OpenSquareBracket => {
         // Array creation
         let mut es = vec![];
         let closing_square_bracket = loop {
            if l.peek_token() == Token::CloseSquareBracket {
               break l.next();
            }
            es.push(parse_expression(l, parse_context, false, expressions)?);
            if l.peek_token() == Token::CloseSquareBracket {
               break l.next();
            }
            expect(l, parse_context, Token::Comma)?;
         };
         let combined_location = merge_locations(expr_begin_token.source_info, closing_square_bracket.source_info);
         wrap(
            Expression::ArrayLiteral(es.into_boxed_slice()),
            combined_location,
            expressions,
         )
      }
      x @ Token::Minus => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, parse_context, r_bp, if_head, expressions)?;
         let combined_location = merge_locations(expr_begin_token.source_info, begin_location);
         wrap(
            Expression::UnaryOperator(UnOp::Negate, rhs),
            combined_location,
            expressions,
         )
      }
      x @ Token::Exclam => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, parse_context, r_bp, if_head, expressions)?;
         let combined_location = merge_locations(expr_begin_token.source_info, begin_location);
         wrap(
            Expression::UnaryOperator(UnOp::Complement, rhs),
            combined_location,
            expressions,
         )
      }
      x @ Token::Amp => {
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, parse_context, r_bp, if_head, expressions)?;
         let combined_location = merge_locations(expr_begin_token.source_info, begin_location);
         wrap(
            Expression::UnaryOperator(UnOp::AddressOf, rhs),
            combined_location,
            expressions,
         )
      }
      x => {
         rolandc_error!(
            &mut parse_context.err_manager,
            expr_begin_token.source_info,
            "While parsing expression, encountered unexpected {}; was expecting a literal, call, variable, or prefix operator",
            x.for_parse_err(),
         );
         return Err(());
      }
   };

   loop {
      let op: Token = match l.peek_token() {
         x @ (Token::Plus
         | Token::Minus
         | Token::Multiply
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
         | Token::Deref
         | Token::OpenSquareBracket
         | Token::ShiftLeft
         | Token::ShiftRight) => x,
         Token::Period => {
            let mut fields = vec![];
            let mut last_location;
            loop {
               let _ = l.next();
               let ident_token = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
               last_location = ident_token.source_info;
               fields.push(extract_identifier(ident_token.token));
               if l.peek_token() != Token::Period {
                  break;
               }
            }
            let combined_location = merge_locations(expr_begin_token.source_info, last_location);
            lhs = wrap(Expression::FieldAccess(fields, lhs), combined_location, expressions);
            continue;
         }
         _ => break,
      };

      if let Some((l_bp, ())) = postfix_binding_power(op) {
         if l_bp < min_bp {
            break;
         }

         let op = l.next();

         lhs = match op.token {
            Token::OpenSquareBracket => {
               let inner = parse_expression(l, parse_context, false, expressions)?;
               let close_token = expect(l, parse_context, Token::CloseSquareBracket)?;
               let combined_location = merge_locations(expr_begin_token.source_info, close_token.source_info);
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
               let a_type = parse_type(l, parse_context)?;
               let combined_location = merge_locations(expr_begin_token.source_info, a_type.location);
               wrap(
                  Expression::Cast {
                     cast_type: CastType::Extend,
                     target_type: a_type.e_type,
                     expr: lhs,
                  },
                  combined_location,
                  expressions,
               )
            }
            Token::KeywordTruncate => {
               let a_type = parse_type(l, parse_context)?;
               let combined_location = merge_locations(expr_begin_token.source_info, a_type.location);
               wrap(
                  Expression::Cast {
                     cast_type: CastType::Truncate,
                     target_type: a_type.e_type,
                     expr: lhs,
                  },
                  combined_location,
                  expressions,
               )
            }
            Token::KeywordTransmute => {
               let a_type = parse_type(l, parse_context)?;
               let combined_location = merge_locations(expr_begin_token.source_info, a_type.location);
               wrap(
                  Expression::Cast {
                     cast_type: CastType::Transmute,
                     target_type: a_type.e_type,
                     expr: lhs,
                  },
                  combined_location,
                  expressions,
               )
            }
            Token::Deref => {
               let combined_location = merge_locations(expr_begin_token.source_info, op.source_info);
               wrap(
                  Expression::UnaryOperator(UnOp::Dereference, lhs),
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

      let next_token = l.next();
      let op = next_token.token;
      let rhs = pratt(l, parse_context, r_b, if_head, expressions)?;

      let bin_op = match op {
         Token::Plus => BinOp::Add,
         Token::Minus => BinOp::Subtract,
         Token::Pipe => BinOp::BitwiseOr,
         Token::Amp => BinOp::BitwiseAnd,
         Token::KeywordOr => BinOp::LogicalOr,
         Token::KeywordAnd => BinOp::LogicalAnd,
         Token::Multiply => BinOp::Multiply,
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
      Token::Exclam => ((), 19),
      Token::Minus => ((), 19),
      Token::Amp => ((), 19),
      _ => unreachable!(),
   }
}

fn postfix_binding_power(op: Token) -> Option<(u8, ())> {
   match &op {
      Token::OpenSquareBracket => Some((21, ())),
      Token::KeywordExtend => Some((18, ())),
      Token::KeywordTruncate => Some((18, ())),
      Token::KeywordTransmute => Some((18, ())),
      Token::Deref => Some((20, ())),
      _ => None,
   }
}

fn infix_binding_power(op: Token) -> (u8, u8) {
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
      Token::Multiply | Token::Divide | Token::Remainder => (16, 17),
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
