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
pub enum ExpressionType {
   Int,
   String,
   Bool,
   Unit,
   CompileError,
}

pub struct ExpressionNode {
   pub expression: Expression,
   pub exp_type: Option<ExpressionType>,
}

pub enum Expression {
   ProcedureCall(String, Vec<ExpressionNode>),
   StringLiteral(String),
   IntLiteral(i64),
   Variable(String),
   BinaryOperator(BinOp, Box<(ExpressionNode, ExpressionNode)>),
   UnaryOperator(UnOp, Box<ExpressionNode>),
}

pub enum Statement {
   ExpressionStatement(ExpressionNode),
   VariableDeclaration(String, ExpressionNode),
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

   Ok(Program { procedures, literals: HashSet::new() })
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
   expect(l, &Token::CloseParen)?;
   let block = parse_block(l)?;
   Ok(ProcedureNode {
      name: extract_identifier(function_name),
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
         Some(Token::CloseBrace) => {
            let _ = l.next();
            break;
         }
         Some(Token::KeywordLet) => {
            let _ = l.next();
            let variable_name = expect(l, &Token::Identifier(String::from("")))?;
            expect(l, &Token::Assignment)?;
            let e = parse_expression(l)?;
            expect(l, &Token::Semicolon)?;
            statements.push(Statement::VariableDeclaration(extract_identifier(variable_name), e));
         }
         Some(Token::Identifier(_))
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

fn parse_arguments(l: &mut Lexer) -> Result<Vec<ExpressionNode>, ()> {
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
            expect(l, &Token::Comma)?;
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

fn parse_expression(l: &mut Lexer) -> Result<ExpressionNode, ()> {
   Ok(wrap(pratt(l, 0)?))
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

      return Ok(Expression::BinaryOperator(bin_op, Box::new((wrap(rhs), wrap(lhs)))));
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

fn wrap(expression: Expression) -> ExpressionNode {
   ExpressionNode {
      expression,
      exp_type: None,
   }
}
