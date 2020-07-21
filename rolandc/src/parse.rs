use super::lex::Token;
use std::collections::HashSet;
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
   pub locals: Vec<(String, ExpressionType)>,
   pub block: BlockNode,
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
}

#[derive(Debug)]
pub enum UnOp {
   Negate,
   LogicalNegate,
}

#[derive(Clone, Debug, PartialEq)]

pub enum IntWidth {
   Eight,
   Four,
   Two,
   One,
}

#[derive(Clone, Debug, PartialEq)]
pub struct IntType {
   pub signed: bool,
   pub width: IntWidth,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExpressionType {
   UnknownInt,
   Int(IntType),
   String,
   Bool,
   Unit,
   CompileError,
}

impl ExpressionType {
   pub fn is_any_known_int(&self) -> bool {
      match self {
         ExpressionType::Int(_) => true,
         _ => false,
      }
   }

   pub fn as_roland_type(&self) -> &str {
      match self {
         ExpressionType::UnknownInt => "?? Int",
         ExpressionType::Int(x) => match (x.signed, &x.width) {
            (true, IntWidth::Eight) => "i64",
            (true, IntWidth::Four) => "i32",
            (true, IntWidth::Two) => "i16",
            (true, IntWidth::One) => "i8",
            (false, IntWidth::Eight) => "u64",
            (false, IntWidth::Four) => "u32",
            (false, IntWidth::Two) => "u16",
            (false, IntWidth::One) => "u8",
         },
         ExpressionType::String => "String",
         ExpressionType::Bool => "bool",
         ExpressionType::Unit => "()",
         ExpressionType::CompileError => "ERROR",
      }
   }
}

pub struct ExpressionNode {
   pub expression: Expression,
   pub exp_type: Option<ExpressionType>,
}

pub enum Expression {
   ProcedureCall(String, Vec<ExpressionNode>),
   BoolLiteral(bool),
   StringLiteral(String),
   IntLiteral(i64),
   Variable(String),
   BinaryOperator(BinOp, Box<(ExpressionNode, ExpressionNode)>),
   UnaryOperator(UnOp, Box<ExpressionNode>),
}

pub enum Statement {
   AssignmentStatement(String, ExpressionNode),
   BlockStatement(BlockNode),
   ExpressionStatement(ExpressionNode),
   IfElseStatement(ExpressionNode, BlockNode, BlockNode),
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
   let block = parse_block(l)?;
   Ok(ProcedureNode {
      name: extract_identifier(function_name),
      parameters,
      locals: Vec::new(),
      block,
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
         Some(Token::KeywordLet) => {
            let mut declared_type = None;
            let _ = l.next();
            let variable_name = expect(l, &Token::Identifier(String::from("")))?;
            let next_discrim = l.peek().map(|x| discriminant(x));
            if next_discrim == Some(discriminant(&Token::Colon)) {
               let _ = l.next();
               let type_token = expect(l, &Token::Identifier(String::from("")))?;
               let type_s = extract_identifier(type_token);
               declared_type = match parse_type(&type_s) {
                  Some(v) => Some(v),
                  None => {
                     eprintln!("While parsing variable declaration - got an invalid type `{}`", type_s);
                     return Err(());
                  }
               };
            }
            expect(l, &Token::Assignment)?;
            let e = parse_expression(l)?;
            expect(l, &Token::Semicolon)?;
            statements.push(Statement::VariableDeclaration(extract_identifier(variable_name), e, declared_type));
         }
         Some(Token::KeywordIf) => {
            let _ = l.next();
            let e = parse_expression(l)?;
            let if_block = parse_block(l)?;
            let else_block = match l.peek() {
               Some(&Token::KeywordElse) => {
                  let _ = l.next();
                  parse_block(l)?
               }
               _ => BlockNode { statements: vec![] },
            };
            statements.push(Statement::IfElseStatement(e, if_block, else_block));
         }
         Some(Token::Identifier(_)) => {
            match l.double_peek() {
               Some(&Token::Assignment) => {
                  let variable_name = expect(l, &Token::Identifier(String::from("")))?;
                  expect(l, &Token::Assignment)?;
                  let e = parse_expression(l)?;
                  expect(l, &Token::Semicolon)?;
                  statements.push(Statement::AssignmentStatement(extract_identifier(variable_name), e));
               }
               _ => {
                  let e = parse_expression(l)?;
                  expect(l, &Token::Semicolon)?;
                  statements.push(Statement::ExpressionStatement(e));
               }
            }
         }
         Some(Token::BoolLiteral(_))
         | Some(Token::StringLiteral(_))
         | Some(Token::IntLiteral(_))
         | Some(Token::OpenParen)
         | Some(Token::Minus) => {
            let e = parse_expression(l)?;
            expect(l, &Token::Semicolon)?;
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

fn parse_parameters(l: &mut Lexer) -> Result<Vec<(String, ExpressionType)>, ()> {
   let mut parameters = vec![];

   loop {
      match l.peek() {
         Some(Token::Identifier(_)) => {
            let id = l.next().unwrap();
            expect(l, &Token::Colon)?;
            let type_token = expect(l, &Token::Identifier(String::from("")))?;
            let type_s = extract_identifier(type_token);
            let e_type = match parse_type(&type_s) {
               Some(v) => v,
               None => {
                  eprintln!("While parsing parameters - got an invalid type `{}`", type_s);
                  return Err(());
               }
            };
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

fn pratt(l: &mut Lexer, min_bp: u8) -> Result<Expression, ()> {
   let lhs = l.next();
   let lhs = match lhs {
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
         Expression::UnaryOperator(UnOp::LogicalNegate, Box::new(wrap(rhs)))
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

      return Ok(Expression::BinaryOperator(bin_op, Box::new((wrap(lhs), wrap(rhs)))));
   }

   Ok(lhs)
}

fn prefix_binding_power(op: &Token) -> ((), u8) {
   match op {
      Token::Exclam => ((), 6),
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

fn parse_type(type_s: &str) -> Option<ExpressionType> {
   match type_s {
      "bool" => Some(ExpressionType::Bool),
      "i64" => Some(ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::Eight,
      })),
      "i32" => Some(ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::Four,
      })),
      "i16" => Some(ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::Two,
      })),
      "i8" => Some(ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::One,
      })),
      "u64" => Some(ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::Eight,
      })),
      "u32" => Some(ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::Four,
      })),
      "u16" => Some(ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::Two,
      })),
      "u8" => Some(ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::One,
      })),
      "String" => Some(ExpressionType::String),
      _ => None,
   }
}

fn wrap(expression: Expression) -> ExpressionNode {
   ExpressionNode {
      expression,
      exp_type: None,
   }
}
