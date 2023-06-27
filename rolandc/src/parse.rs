use std::collections::HashMap;
use std::mem::discriminant;

use indexmap::{IndexMap, IndexSet};
use slotmap::{new_key_type, SecondaryMap, SlotMap};

use super::lex::{SourceToken, Token};
use crate::error_handling::error_handling_macros::rolandc_error;
use crate::error_handling::ErrorManager;
use crate::interner::{Interner, StrId, DUMMY_STR_TOKEN};
use crate::lex::Lexer;
use crate::semantic_analysis::{EnumInfo, GlobalInfo, GlobalKind, ProcedureInfo, StructInfo};
use crate::size_info::SizeInfo;
use crate::source_info::SourceInfo;
use crate::type_data::ExpressionType;

new_key_type! { pub struct ExpressionId; }
pub type ExpressionPool = SlotMap<ExpressionId, ExpressionNode>;

new_key_type! { pub struct StatementId; }
pub type StatementPool = SlotMap<StatementId, StatementNode>;

#[derive(Clone)]
pub struct AstPool {
   pub statements: StatementPool,
   pub expressions: ExpressionPool,
}

fn merge_locations(begin: SourceInfo, end: SourceInfo) -> SourceInfo {
   SourceInfo {
      begin: begin.begin,
      end: end.end,
      file: begin.file,
   }
}

fn expect(l: &mut Lexer, parse_context: &mut ParseContext, token: Token) -> Result<SourceToken, ()> {
   let lex_token = l.peek_token();
   if discriminant(&lex_token) == discriminant(&token) {
      Ok(l.next())
   } else {
      rolandc_error!(
         &mut parse_context.err_manager,
         l.peek_source(),
         "Encountered {} when expecting {}",
         lex_token.for_parse_err(),
         token.for_parse_err()
      );
      Err(())
   }
}

#[derive(Clone)]
pub struct ProcedureDefinition {
   pub name: StrNode,
   pub generic_parameters: Vec<StrNode>,
   pub constraints: IndexMap<StrId, IndexSet<StrId>>,
   pub parameters: Vec<ParameterNode>,
   pub ret_type: ExpressionTypeNode,
}

#[derive(Clone)]
pub struct ProcedureNode {
   pub definition: ProcedureDefinition,
   pub location: SourceInfo,
   pub proc_impl: ProcImplSource,

   pub locals: IndexMap<VariableId, ExpressionType>,
}

#[derive(Clone)]
pub enum ProcImplSource {
   Builtin,
   External,
   Body(BlockNode),
}

#[derive(Clone)]
pub struct ParameterNode {
   pub name: StrId,
   pub p_type: ExpressionTypeNode,
   pub var_id: VariableId,
   pub named: bool,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct StructNode {
   pub name: StrId,
   pub fields: Vec<(StrId, ExpressionTypeNode, Option<ExpressionId>)>,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct EnumNode {
   pub name: StrId,
   pub requested_size: Option<ExpressionTypeNode>,
   pub variants: Vec<StrNode>,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct ConstNode {
   pub name: StrNode,
   pub var_id: VariableId,
   pub const_type: ExpressionTypeNode,
   pub value: ExpressionId,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct StaticNode {
   pub name: StrNode,
   pub static_type: ExpressionTypeNode,
   pub value: Option<ExpressionId>,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct ExpressionTypeNode {
   pub e_type: ExpressionType,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct TraitNode {
   pub name: StrNode,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CastType {
   As,
   Transmute,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct VariableId(u64);

impl VariableId {
   #[must_use]
   pub fn first() -> VariableId {
      VariableId(0)
   }

   #[must_use]
   pub fn next(&self) -> VariableId {
      VariableId(self.0 + 1)
   }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
   ProcedureCall {
      proc_expr: ExpressionId,
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
   UnresolvedVariable(StrNode),
   Variable(VariableId),
   BinaryOperator {
      operator: BinOp,
      lhs: ExpressionId,
      rhs: ExpressionId,
   },
   UnaryOperator(UnOp, ExpressionId),
   UnresolvedStructLiteral(StrNode, Box<[(StrId, Option<ExpressionId>)]>),
   StructLiteral(StrNode, IndexMap<StrId, Option<ExpressionId>>),
   FieldAccess(Vec<StrId>, ExpressionId),
   Cast {
      cast_type: CastType,
      target_type: ExpressionType,
      expr: ExpressionId,
   },
   EnumLiteral(StrNode, StrNode),
   UnresolvedProcLiteral(StrNode, Vec<GenericArgumentNode>),
   BoundFcnLiteral(ProcedureId, Box<[GenericArgumentNode]>),
   IfX(ExpressionId, ExpressionId, ExpressionId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgumentNode {
   pub name: Option<StrId>,
   pub expr: ExpressionId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericArgumentNode {
   pub gtype: ExpressionType,
   pub location: SourceInfo,
}

impl Expression {
   #[must_use]
   pub fn is_lvalue(&self, expressions: &ExpressionPool, global_info: &IndexMap<VariableId, GlobalInfo>) -> bool {
      match self {
         Expression::Variable(x) => global_info.get(x).map_or(true, |x| x.kind != GlobalKind::Const),
         Expression::ArrayIndex { array, .. } => expressions[*array].expression.is_lvalue(expressions, global_info),
         Expression::UnaryOperator(UnOp::Dereference, _) => true,
         Expression::FieldAccess(_, lhs) => expressions[*lhs].expression.is_lvalue(expressions, global_info),
         Expression::UnresolvedVariable(_) => unreachable!(),
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
         Expression::UnresolvedVariable(_) => unreachable!(),
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
   For {
      induction_var_name: StrNode,
      range_start: ExpressionId,
      range_end: ExpressionId,
      body: BlockNode,
      range_inclusive: bool,
      induction_var: VariableId,
   },
   Continue,
   Break,
   Defer(StatementId),
   Expression(ExpressionId),
   IfElse(ExpressionId, BlockNode, StatementId),
   Return(ExpressionId),
   VariableDeclaration(StrNode, Option<ExpressionId>, Option<ExpressionTypeNode>, VariableId),
}

// For lack of a better place...
#[must_use]
pub fn statement_always_returns(stmt: StatementId, ast: &AstPool) -> bool {
   match &ast.statements[stmt].statement {
      Statement::Return(_) => true,
      Statement::IfElse(_, then_block, else_if) => {
         then_block
            .statements
            .last()
            .map_or(false, |l| statement_always_returns(*l, ast))
            && statement_always_returns(*else_if, ast)
      }
      Statement::Block(bn) => bn
         .statements
         .last()
         .map_or(false, |l| statement_always_returns(*l, ast)),
      Statement::Expression(ex) => *ast.expressions[*ex].exp_type.as_ref().unwrap() == ExpressionType::Never,
      _ => false,
   }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StrNode {
   pub str: StrId,
   pub location: SourceInfo,
}

#[derive(Clone, Debug)]
pub struct ImportNode {
   pub import_path: StrNode,
   pub location: SourceInfo,
}

#[derive(Clone)]
pub struct BlockNode {
   pub statements: Vec<StatementId>,
   pub location: SourceInfo,
}

new_key_type! { pub struct StaticId; }
new_key_type! { pub struct ProcedureId; }

#[derive(Clone)]
pub struct Program {
   // These fields are populated by the parser
   pub enums: Vec<EnumNode>,
   pub procedures: SlotMap<ProcedureId, ProcedureNode>,
   pub structs: Vec<StructNode>,
   pub consts: Vec<ConstNode>,
   pub statics: Vec<StaticNode>,
   pub ast: AstPool,

   // (only read by the language server)
   pub source_to_definition: IndexMap<SourceInfo, SourceInfo>,
   pub parsed_types: Vec<ExpressionTypeNode>,

   // These fields are populated during semantic analysis
   pub literals: IndexSet<StrId>,
   pub enum_info: IndexMap<StrId, EnumInfo>,
   pub struct_info: IndexMap<StrId, StructInfo>,
   pub global_info: IndexMap<VariableId, GlobalInfo>,
   pub procedure_info: SecondaryMap<ProcedureId, ProcedureInfo>,
   pub procedure_name_table: HashMap<StrId, ProcedureId>, // TODO: this doesn't need to live on Program
   pub struct_size_info: HashMap<StrId, SizeInfo>,
   pub next_variable: VariableId,
}

// SlotMaps are deterministic, but the order that you get after clearing it is not the same as you would get
// from a new SlotMap. To preserve determinism when the compiler is invoked multiple times with the same context,
// we reset SlotMaps this (more expensive) way.
fn reset_slotmap<K: slotmap::Key, V>(s: &mut SlotMap<K, V>) {
   let old_cap = s.capacity();
   let new_map = SlotMap::with_capacity_and_key(old_cap);
   *s = new_map;
}

fn reset_secondarymap<K: slotmap::Key, V>(s: &mut SecondaryMap<K, V>) {
   let old_cap = s.capacity();
   let new_map = SecondaryMap::with_capacity(old_cap);
   *s = new_map;
}

impl Program {
   #[must_use]
   pub fn new() -> Program {
      Program {
         enums: Vec::new(),
         procedures: SlotMap::with_key(),
         structs: Vec::new(),
         consts: Vec::new(),
         statics: Vec::new(),
         parsed_types: Vec::new(),
         literals: IndexSet::new(),
         enum_info: IndexMap::new(),
         struct_info: IndexMap::new(),
         global_info: IndexMap::new(),
         procedure_info: SecondaryMap::new(),
         procedure_name_table: HashMap::new(),
         struct_size_info: HashMap::new(),
         source_to_definition: IndexMap::new(),
         next_variable: VariableId::first(),
         ast: AstPool {
            expressions: ExpressionPool::with_key(),
            statements: StatementPool::with_key(),
         },
      }
   }

   pub fn clear(&mut self) {
      self.enums.clear();
      reset_slotmap(&mut self.procedures);
      self.structs.clear();
      self.consts.clear();
      self.statics.clear();
      self.parsed_types.clear();
      self.literals.clear();
      self.enum_info.clear();
      self.struct_info.clear();
      self.global_info.clear();
      reset_secondarymap(&mut self.procedure_info);
      self.procedure_name_table.clear();
      self.struct_size_info.clear();
      self.source_to_definition.clear();
      reset_slotmap(&mut self.ast.expressions);
      reset_slotmap(&mut self.ast.statements);
      self.next_variable = VariableId::first();
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
         | Token::KeywordIfx
   )
}

struct ParseContext<'a> {
   err_manager: &'a mut ErrorManager,
   interner: &'a Interner,
   parsed_types: &'a mut Vec<ExpressionTypeNode>,
}

fn parse_top_level_items(
   lexer: &mut Lexer,
   parse_context: &mut ParseContext,
   ast: &mut AstPool,
   top: &mut TopLevelItems,
) -> Result<(), ()> {
   loop {
      let peeked_token = lexer.peek_token();
      match peeked_token {
         Token::KeywordExtern => {
            let extern_kw = lexer.next();
            expect(lexer, parse_context, Token::KeywordProc)?;
            let p = parse_external_procedure(lexer, parse_context, extern_kw.source_info, ProcImplSource::External)?;
            top.procedures.insert(p);
         }
         Token::KeywordBuiltin => {
            let builtin_kw = lexer.next();
            expect(lexer, parse_context, Token::KeywordProc)?;
            let p = parse_external_procedure(lexer, parse_context, builtin_kw.source_info, ProcImplSource::Builtin)?;
            top.procedures.insert(p);
         }
         Token::KeywordProc => {
            let def = lexer.next();
            let p = parse_procedure(lexer, parse_context, def.source_info, ast)?;
            top.procedures.insert(p);
         }
         Token::KeywordImport => {
            let kw = lexer.next();
            let import_path = parse_string(lexer, parse_context)?;
            let sc = expect(lexer, parse_context, Token::Semicolon)?;
            top.imports.push(ImportNode {
               import_path,
               location: merge_locations(kw.source_info, sc.source_info),
            });
         }
         Token::KeywordStructDef => {
            let def = lexer.next();
            let s = parse_struct(lexer, parse_context, def.source_info, &mut ast.expressions)?;
            top.structs.push(s);
         }
         Token::KeywordEnumDef => {
            let def = lexer.next();
            let s = parse_enum(lexer, parse_context, def.source_info)?;
            top.enums.push(s);
         }
         Token::KeywordConst => {
            let a_const = lexer.next();
            let variable_name = parse_identifier(lexer, parse_context)?;
            expect(lexer, parse_context, Token::Colon)?;
            let const_type = parse_type(lexer, parse_context)?;
            expect(lexer, parse_context, Token::Assignment)?;
            let exp = parse_expression(lexer, parse_context, false, &mut ast.expressions)?;
            let end_token = expect(lexer, parse_context, Token::Semicolon)?;
            top.consts.push(ConstNode {
               name: variable_name,
               const_type,
               location: merge_locations(a_const.source_info, end_token.source_info),
               value: exp,
               var_id: VariableId::first(),
            });
         }
         Token::KeywordStatic => {
            let a_static = lexer.next();
            let variable_name = parse_identifier(lexer, parse_context)?;
            expect(lexer, parse_context, Token::Colon)?;
            let static_type = parse_type(lexer, parse_context)?;
            expect(lexer, parse_context, Token::Assignment)?;
            let exp = if lexer.peek_token() == Token::TripleUnderscore {
               let _ = lexer.next();
               None
            } else {
               Some(parse_expression(lexer, parse_context, false, &mut ast.expressions)?)
            };
            let end_token = expect(lexer, parse_context, Token::Semicolon)?;
            top.statics.push(StaticNode {
               name: variable_name,
               static_type,
               location: merge_locations(a_static.source_info, end_token.source_info),
               value: exp,
            });
         }
         Token::Eof => {
            break;
         }
         x => {
            rolandc_error!(
            parse_context.err_manager,
            lexer.peek_source(),
            "While parsing top level, encountered unexpected {}; was expecting a procedure, const, static, enum, or struct declaration",
            x.for_parse_err()
         );
            return Err(());
         }
      }
   }
   Ok(())
}

struct TopLevelItems<'a> {
   procedures: &'a mut SlotMap<ProcedureId, ProcedureNode>,
   structs: &'a mut Vec<StructNode>,
   enums: &'a mut Vec<EnumNode>,
   consts: &'a mut Vec<ConstNode>,
   statics: &'a mut Vec<StaticNode>,
   imports: Vec<ImportNode>,
}

pub fn astify(
   mut lexer: Lexer,
   err_manager: &mut ErrorManager,
   interner: &Interner,
   program: &mut Program,
) -> Result<Vec<ImportNode>, ()> {
   let mut parse_context = ParseContext {
      err_manager,
      interner,
      parsed_types: &mut program.parsed_types,
   };

   let mut top = TopLevelItems {
      procedures: &mut program.procedures,
      structs: &mut program.structs,
      enums: &mut program.enums,
      consts: &mut program.consts,
      statics: &mut program.statics,
      imports: vec![],
   };

   while parse_top_level_items(&mut lexer, &mut parse_context, &mut program.ast, &mut top).is_err() {
      // skip tokens until we get to a token that must be at the top level and continue parsing
      // in order to give the user more valid errors
      loop {
         match lexer.peek_token() {
            Token::KeywordProc
            | Token::KeywordConst
            | Token::KeywordStatic
            | Token::KeywordImport
            | Token::KeywordStructDef
            | Token::KeywordEnumDef
            | Token::KeywordBuiltin
            | Token::KeywordExtern => break,
            Token::Eof => break,
            _ => {
               let _ = lexer.next();
               continue;
            }
         }
      }
   }

   Ok(top.imports)
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

fn parse_identifier(l: &mut Lexer, parse_context: &mut ParseContext) -> Result<StrNode, ()> {
   let ident = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
   Ok(StrNode {
      str: extract_identifier(ident.token),
      location: ident.source_info,
   })
}

fn parse_string(l: &mut Lexer, parse_context: &mut ParseContext) -> Result<StrNode, ()> {
   let string = expect(l, parse_context, Token::StringLiteral(DUMMY_STR_TOKEN))?;
   Ok(StrNode {
      str: extract_str_literal(string.token),
      location: string.source_info,
   })
}

fn parse_procedure_definition(l: &mut Lexer, parse_context: &mut ParseContext) -> Result<ProcedureDefinition, ()> {
   let procedure_name = parse_identifier(l, parse_context)?;
   let mut generic_parameters = vec![];
   while l.peek_token() == Token::Dollar {
      let _ = l.next();
      let gtype_definition = parse_identifier(l, parse_context)?;
      generic_parameters.push(gtype_definition);
   }
   expect(l, parse_context, Token::OpenParen)?;
   let parameters = parse_parameters(l, parse_context)?;
   let close_paren = expect(l, parse_context, Token::CloseParen)?;
   let ret_type = if l.peek_token() == Token::Arrow {
      let _ = l.next();
      parse_type(l, parse_context)?
   } else {
      ExpressionTypeNode {
         e_type: ExpressionType::Unit,
         // this location is somewhat bogus. ok for now?
         location: merge_locations(procedure_name.location, close_paren.source_info),
      }
   };
   let mut constraints = IndexMap::new();
   if l.peek_token() == Token::KeywordWhere {
      let _ = l.next();
      loop {
         let corresponding_generic_param = parse_identifier(l, parse_context)?;
         expect(l, parse_context, Token::Colon)?;
         let trait_constraint = parse_identifier(l, parse_context)?;
         constraints
            .entry(corresponding_generic_param.str)
            .or_insert_with(IndexSet::new)
            .insert(trait_constraint.str);
         if l.peek_token() == Token::Comma {
            let _ = l.next();
         } else {
            break;
         }
      }
   }
   Ok(ProcedureDefinition {
      name: procedure_name,
      generic_parameters,
      constraints,
      parameters,
      ret_type,
   })
}

fn parse_procedure(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   source_info: SourceInfo,
   ast: &mut AstPool,
) -> Result<ProcedureNode, ()> {
   let definition = parse_procedure_definition(l, parse_context)?;
   let block = parse_block(l, parse_context, ast)?;
   let combined_location = merge_locations(source_info, block.location);
   Ok(ProcedureNode {
      definition,
      locals: IndexMap::new(),
      proc_impl: ProcImplSource::Body(block),
      location: combined_location,
   })
}

fn parse_external_procedure(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   source_info: SourceInfo,
   proc_impl_source: ProcImplSource,
) -> Result<ProcedureNode, ()> {
   let definition = parse_procedure_definition(l, parse_context)?;
   let end_token = expect(l, parse_context, Token::Semicolon)?;
   Ok(ProcedureNode {
      definition,
      location: merge_locations(source_info, end_token.source_info),
      proc_impl: proc_impl_source,
      locals: IndexMap::new(),
   })
}

fn parse_struct(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   source_info: SourceInfo,
   expressions: &mut ExpressionPool,
) -> Result<StructNode, ()> {
   let struct_name = extract_identifier(expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?.token);
   expect(l, parse_context, Token::OpenBrace)?;
   let mut fields: Vec<(StrId, ExpressionTypeNode, Option<ExpressionId>)> = vec![];
   let close_brace = loop {
      if l.peek_token() == Token::CloseBrace {
         break l.next();
      }
      let identifier = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
      let _ = expect(l, parse_context, Token::Colon)?;
      let f_type = parse_type(l, parse_context)?;

      let default_value = if l.peek_token() == Token::Assignment {
         let _ = l.next();
         Some(parse_expression(l, parse_context, false, expressions)?)
      } else {
         None
      };

      fields.push((extract_identifier(identifier.token), f_type, default_value));

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

fn parse_enum(l: &mut Lexer, parse_context: &mut ParseContext, source_info: SourceInfo) -> Result<EnumNode, ()> {
   let enum_name = extract_identifier(expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?.token);
   let requested_size = if l.peek_token() == Token::Colon {
      let _ = l.next();
      Some(parse_type(l, parse_context)?)
   } else {
      None
   };
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
      requested_size,
      location: merge_locations(source_info, close_brace.source_info),
   })
}

fn parse_block(l: &mut Lexer, parse_context: &mut ParseContext, ast: &mut AstPool) -> Result<BlockNode, ()> {
   let open_brace = expect(l, parse_context, Token::OpenBrace)?;

   let mut statements: Vec<StatementId> = vec![];

   let close_brace = 'outer: loop {
      match parse_semicolon_terminated_statement(l, parse_context, ast) {
         Ok(None) => (),
         Ok(Some(s)) => {
            statements.push(s);
            continue;
         }
         Err(e) => loop {
            match l.peek_token() {
               Token::Semicolon => {
                  let _ = l.next();
                  continue 'outer;
               }
               // Token unambiguously begins a new statement
               Token::KeywordLet
               | Token::KeywordFor
               | Token::KeywordBreak
               | Token::KeywordContinue
               | Token::KeywordDefer
               | Token::KeywordIf
               | Token::KeywordLoop
               | Token::KeywordReturn => {
                  continue 'outer;
               }
               Token::CloseBrace => {
                  break 'outer l.next();
               }
               Token::Eof => return Err(e),
               _ => {
                  let _ = l.next();
               }
            }
         },
      }

      if let Some(s) = parse_blocky_statement(l, parse_context, ast)? {
         statements.push(s);
         continue;
      }

      match l.peek_token() {
         Token::CloseBrace => {
            break l.next();
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

fn parse_statement(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   ast: &mut AstPool,
) -> Result<Option<StatementId>, ()> {
   if let Some(s) = parse_semicolon_terminated_statement(l, parse_context, ast)? {
      return Ok(Some(s));
   }
   if let Some(s) = parse_blocky_statement(l, parse_context, ast)? {
      return Ok(Some(s));
   }
   Ok(None)
}

fn parse_semicolon_terminated_statement(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   ast: &mut AstPool,
) -> Result<Option<StatementId>, ()> {
   let next = l.peek_token();
   let begin_source = l.peek_source();
   let stmt = match next {
      Token::KeywordContinue => {
         let _ = l.next();
         Statement::Continue
      }
      Token::KeywordBreak => {
         let _ = l.next();
         Statement::Break
      }
      Token::KeywordReturn => {
         let _ = l.next();
         let e = if l.peek_token() == Token::Semicolon {
            wrap(Expression::UnitLiteral, begin_source, &mut ast.expressions)
         } else {
            parse_expression(l, parse_context, false, &mut ast.expressions)?
         };
         Statement::Return(e)
      }
      Token::KeywordDefer => {
         let _ = l.next();
         let opt_stmt = parse_statement(l, parse_context, ast)?;

         if let Some(stmt) = opt_stmt {
            return Ok(Some(ast.statements.insert(StatementNode {
               statement: Statement::Defer(stmt),
               location: merge_locations(begin_source, ast.statements[stmt].location),
            })));
         }

         rolandc_error!(
            &mut parse_context.err_manager,
            l.peek_source(),
            "While parsing defer, encountered unexpected {}; was expecting a statement",
            l.peek_token().for_parse_err()
         );
         return Err(());
      }
      Token::KeywordLet => {
         let _ = l.next();
         let mut declared_type = None;
         let variable_name = parse_identifier(l, parse_context)?;
         if l.peek_token() == Token::Colon {
            let _ = l.next();
            declared_type = Some(parse_type(l, parse_context)?);
         }
         expect(l, parse_context, Token::Assignment)?;
         let e = if l.peek_token() == Token::TripleUnderscore {
            let _ = l.next();
            None
         } else {
            Some(parse_expression(l, parse_context, false, &mut ast.expressions)?)
         };
         Statement::VariableDeclaration(variable_name, e, declared_type, VariableId::first())
      }
      x if token_starts_expression(x) => {
         let e = parse_expression(l, parse_context, false, &mut ast.expressions)?;
         match l.peek_token() {
            Token::Assignment => {
               let _ = l.next();
               let re = parse_expression(l, parse_context, false, &mut ast.expressions)?;
               Statement::Assignment(e, re)
            }
            Token::Semicolon => Statement::Expression(e),
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
      _ => return Ok(None),
   };

   let sc = expect(l, parse_context, Token::Semicolon)?;

   Ok(Some(ast.statements.insert(StatementNode {
      statement: stmt,
      location: merge_locations(begin_source, sc.source_info),
   })))
}

fn parse_blocky_statement(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   ast: &mut AstPool,
) -> Result<Option<StatementId>, ()> {
   match l.peek_token() {
      Token::OpenBrace => {
         let source = l.peek_source();
         let new_block = parse_block(l, parse_context, ast)?;
         let id = ast.statements.insert(StatementNode {
            statement: Statement::Block(new_block),
            location: source,
         });
         Ok(Some(id))
      }
      Token::KeywordFor => {
         let for_token = l.next();
         let variable_name = parse_identifier(l, parse_context)?;
         let _ = expect(l, parse_context, Token::KeywordIn)?;
         let start_en = parse_expression(l, parse_context, true, &mut ast.expressions)?;
         let _ = expect(l, parse_context, Token::DoublePeriod)?;
         let inclusive = if l.peek_token() == Token::Assignment {
            let _ = l.next();
            true
         } else {
            false
         };
         let end_en = parse_expression(l, parse_context, true, &mut ast.expressions)?;
         let new_block = parse_block(l, parse_context, ast)?;
         let id = ast.statements.insert(StatementNode {
            statement: Statement::For {
               induction_var_name: variable_name,
               range_start: start_en,
               range_end: end_en,
               body: new_block,
               range_inclusive: inclusive,
               induction_var: VariableId::first(),
            },
            location: for_token.source_info,
         });
         Ok(Some(id))
      }
      Token::KeywordLoop => {
         let loop_token = l.next();
         let new_block = parse_block(l, parse_context, ast)?;
         let id = ast.statements.insert(StatementNode {
            statement: Statement::Loop(new_block),
            location: loop_token.source_info,
         });
         Ok(Some(id))
      }
      Token::KeywordIf => {
         let s = parse_if_else_statement(l, parse_context, ast)?;
         Ok(Some(s))
      }
      _ => Ok(None),
   }
}

fn parse_if_else_statement(
   l: &mut Lexer,
   parse_context: &mut ParseContext,
   ast: &mut AstPool,
) -> Result<StatementId, ()> {
   let if_token = l.next();
   let e = parse_expression(l, parse_context, true, &mut ast.expressions)?;
   let if_block = parse_block(l, parse_context, ast)?;
   let else_statement = match (l.peek_token(), l.double_peek_token()) {
      (Token::KeywordElse, Token::KeywordIf) => {
         let _ = l.next();
         parse_if_else_statement(l, parse_context, ast)?
      }
      (Token::KeywordElse, _) => {
         let else_token = l.next();
         let n = StatementNode {
            statement: Statement::Block(parse_block(l, parse_context, ast)?),
            location: else_token.source_info,
         };
         ast.statements.insert(n)
      }
      _ => ast.statements.insert(StatementNode {
         statement: Statement::Block(BlockNode {
            statements: vec![],
            location: if_block.location,
         }),
         location: if_token.source_info,
      }),
   };
   let combined_location = merge_locations(if_token.source_info, ast.statements[else_statement].location);
   Ok(ast.statements.insert(StatementNode {
      statement: Statement::IfElse(e, if_block, else_statement),
      location: combined_location,
   }))
}

fn parse_parameters(l: &mut Lexer, parse_context: &mut ParseContext) -> Result<Vec<ParameterNode>, ()> {
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
            let e_type = parse_type(l, parse_context)?;
            parameters.push(ParameterNode {
               name: extract_identifier(id.token),
               location: id.source_info,
               p_type: e_type,
               var_id: VariableId::first(),
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

fn parse_generic_arguments(l: &mut Lexer, parse_context: &mut ParseContext) -> Result<Vec<GenericArgumentNode>, ()> {
   let mut generic_arguments = vec![];

   while l.peek_token() == Token::Dollar {
      let dollar = l.next();
      let gtype = parse_type(l, parse_context)?;
      let combined_location = merge_locations(dollar.source_info, gtype.location);
      generic_arguments.push(GenericArgumentNode {
         gtype: gtype.e_type,
         location: combined_location,
      });
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

   let (loc_end, mut value_type) = match l.peek_token() {
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
               ExpressionType::Array(Box::new(a_inner_type.e_type), valid_arr_len),
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
      Token::Exclam => {
         let token = l.next();
         (token.source_info, ExpressionType::Never)
      }
      Token::KeywordProc => {
         let _ = l.next();
         expect(l, parse_context, Token::OpenParen)?;
         let mut parameters = vec![];
         loop {
            if l.peek_token() == Token::CloseParen {
               break;
            }
            parameters.push(parse_type(l, parse_context)?.e_type);
            if l.peek_token() == Token::CloseParen {
               break;
            }
            expect(l, parse_context, Token::Comma)?;
         }
         let close_paren = expect(l, parse_context, Token::CloseParen)?;
         let (return_type, last_location) = if l.peek_token() == Token::Arrow {
            let _ = l.next();
            let return_type_p = parse_type(l, parse_context)?;
            (return_type_p.e_type, return_type_p.location)
         } else {
            (ExpressionType::Unit, close_paren.source_info)
         };
         (
            last_location,
            ExpressionType::ProcedurePointer {
               parameters: parameters.into_boxed_slice(),
               ret_type: Box::new(return_type),
            },
         )
      }
      _ => {
         let type_token = expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?;
         let type_s = extract_identifier(type_token.token);
         (
            type_token.source_info,
            match parse_context.interner.lookup(type_s) {
               "bool" => ExpressionType::Bool,
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
               "unit" => ExpressionType::Unit,
               _ => ExpressionType::Unresolved(type_s),
            },
         )
      }
   };

   while ptr_count > 0 {
      value_type = ExpressionType::Pointer(Box::new(value_type));
      ptr_count -= 1;
   }

   let etn = ExpressionTypeNode {
      e_type: value_type,
      location: merge_locations(loc_start, loc_end),
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
   let begin_source = l.peek_source();
   let mut lhs = match l.peek_token() {
      Token::BoolLiteral(x) => {
         let _ = l.next();
         wrap(Expression::BoolLiteral(x), begin_source, expressions)
      }
      Token::IntLiteral(x) => {
         let _ = l.next();
         wrap(
            Expression::IntLiteral {
               val: x,
               synthetic: false,
            },
            begin_source,
            expressions,
         )
      }
      Token::FloatLiteral(x) => {
         let _ = l.next();
         wrap(Expression::FloatLiteral(x), begin_source, expressions)
      }
      Token::StringLiteral(x) => {
         let _ = l.next();
         wrap(Expression::StringLiteral(x), begin_source, expressions)
      }
      Token::Identifier(s) => {
         let _ = l.next();
         if l.peek_token() == Token::Dollar {
            let generic_args = parse_generic_arguments(l, parse_context)?;
            let combined_location = merge_locations(begin_source, generic_args.last().as_ref().unwrap().location);
            wrap(
               Expression::UnresolvedProcLiteral(
                  StrNode {
                     str: s,
                     location: begin_source,
                  },
                  generic_args,
               ),
               combined_location,
               expressions,
            )
         } else if l.peek_token() == Token::DoubleColon {
            let _ = l.next();
            let variant = parse_identifier(l, parse_context)?;
            let combined_location = merge_locations(begin_source, variant.location);
            wrap(
               Expression::EnumLiteral(
                  StrNode {
                     str: s,
                     location: begin_source,
                  },
                  variant,
               ),
               combined_location,
               expressions,
            )
         } else if !if_head && l.peek_token() == Token::OpenBrace {
            let _ = l.next();
            let mut fields: Vec<(StrId, Option<ExpressionId>)> = vec![];
            let close_brace = loop {
               if l.peek_token() == Token::CloseBrace {
                  break l.next();
               }
               let identifier = extract_identifier(expect(l, parse_context, Token::Identifier(DUMMY_STR_TOKEN))?.token);
               let _ = expect(l, parse_context, Token::Colon)?;
               let val = if l.peek_token() == Token::TripleUnderscore {
                  let _ = l.next();
                  None
               } else {
                  Some(parse_expression(l, parse_context, false, expressions)?)
               };
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
            let combined_location = merge_locations(begin_source, close_brace.source_info);
            wrap(
               Expression::UnresolvedStructLiteral(
                  StrNode {
                     str: s,
                     location: begin_source,
                  },
                  fields.into_boxed_slice(),
               ),
               combined_location,
               expressions,
            )
         } else {
            wrap(
               Expression::UnresolvedVariable(StrNode {
                  str: s,
                  location: begin_source,
               }),
               begin_source,
               expressions,
            )
         }
      }
      Token::OpenParen => {
         let _ = l.next();
         let new_lhs = pratt(l, parse_context, 0, false, expressions)?;
         expect(l, parse_context, Token::CloseParen)?;
         new_lhs
      }
      Token::KeywordIfx => {
         let _ = l.next();
         let condition = parse_expression(l, parse_context, false, expressions)?;
         let consequent = parse_expression(l, parse_context, false, expressions)?;
         expect(l, parse_context, Token::KeywordElse)?;
         let otherwise = parse_expression(l, parse_context, false, expressions)?;
         let combined_location = merge_locations(begin_source, expressions[otherwise].location);
         wrap(
            Expression::IfX(condition, consequent, otherwise),
            combined_location,
            expressions,
         )
      }
      Token::OpenSquareBracket => {
         let _ = l.next();
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
         let combined_location = merge_locations(begin_source, closing_square_bracket.source_info);
         wrap(
            Expression::ArrayLiteral(es.into_boxed_slice()),
            combined_location,
            expressions,
         )
      }
      x @ Token::Minus => {
         let _ = l.next();
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, parse_context, r_bp, if_head, expressions)?;
         let combined_location = merge_locations(begin_source, begin_location);
         wrap(
            Expression::UnaryOperator(UnOp::Negate, rhs),
            combined_location,
            expressions,
         )
      }
      x @ Token::Exclam => {
         let _ = l.next();
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, parse_context, r_bp, if_head, expressions)?;
         let combined_location = merge_locations(begin_source, begin_location);
         wrap(
            Expression::UnaryOperator(UnOp::Complement, rhs),
            combined_location,
            expressions,
         )
      }
      x @ Token::Amp => {
         let _ = l.next();
         let ((), r_bp) = prefix_binding_power(&x);
         let begin_location = l.peek_source();
         let rhs = pratt(l, parse_context, r_bp, if_head, expressions)?;
         let combined_location = merge_locations(begin_source, begin_location);
         wrap(
            Expression::UnaryOperator(UnOp::AddressOf, rhs),
            combined_location,
            expressions,
         )
      }
      x => {
         rolandc_error!(
            &mut parse_context.err_manager,
            begin_source,
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
         | Token::KeywordAs
         | Token::KeywordTransmute
         | Token::Deref
         | Token::OpenSquareBracket
         | Token::OpenParen
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
            let combined_location = merge_locations(begin_source, last_location);
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
            Token::OpenParen => {
               let args = parse_arguments(l, parse_context, expressions)?;
               let close_token = expect(l, parse_context, Token::CloseParen)?;
               let combined_location = merge_locations(begin_source, close_token.source_info);
               wrap(
                  Expression::ProcedureCall {
                     proc_expr: lhs,
                     args: args.into_boxed_slice(),
                  },
                  combined_location,
                  expressions,
               )
            }
            Token::OpenSquareBracket => {
               let inner = parse_expression(l, parse_context, false, expressions)?;
               let close_token = expect(l, parse_context, Token::CloseSquareBracket)?;
               let combined_location = merge_locations(begin_source, close_token.source_info);
               wrap(
                  Expression::ArrayIndex {
                     array: lhs,
                     index: inner,
                  },
                  combined_location,
                  expressions,
               )
            }
            Token::KeywordAs => {
               let a_type = parse_type(l, parse_context)?;
               let combined_location = merge_locations(begin_source, a_type.location);
               wrap(
                  Expression::Cast {
                     cast_type: CastType::As,
                     target_type: a_type.e_type,
                     expr: lhs,
                  },
                  combined_location,
                  expressions,
               )
            }
            Token::KeywordTransmute => {
               let a_type = parse_type(l, parse_context)?;
               let combined_location = merge_locations(begin_source, a_type.location);
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
               let combined_location = merge_locations(begin_source, op.source_info);
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
      Token::OpenParen => Some((21, ())),
      Token::OpenSquareBracket => Some((21, ())),
      Token::KeywordAs => Some((18, ())),
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
   expressions.insert(ExpressionNode {
      expression,
      exp_type: None,
      location: source_info,
   })
}
