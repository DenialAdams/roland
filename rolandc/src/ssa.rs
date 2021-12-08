use crate::interner::StrId;
use crate::parse::{BlockNode, Expression, ExpressionNode, Program, Statement, BinOp, UnOp};
use std::collections::HashMap;
use std::io::Write;

enum Instruction {
   UnaryExpression(UnOp, usize),
   BinaryExpression(BinOp, usize, usize),
   IntLiteral(i128),
   Phi(Vec<usize>),
   Jump(usize),
   Branch(usize, usize),
   Return,
}

impl Instruction {
   /// This asserts that the instruction is a Phi function
   fn get_phi_operands(&mut self) -> &mut Vec<usize> {
      match self {
         Instruction::Phi(x) => x,
         _ => unreachable!(),
      }
   }
}

struct SsaContext {
   sealed: Vec<bool>,
   // variables in each basic block, as an index into values
   current_defs: Vec<HashMap<StrId, usize>>,
   values: Vec<Instruction>,
   cur_block: usize,
   incomplete_phis: Vec<Vec<usize>>,
}

// This structure is separate from SSAContext due to rust borrowing restrictions :(
struct Cfg {
   predecessors: Vec<Vec<usize>>,
   successors: Vec<Vec<usize>>,
}

fn new_basic_block(cfg: &mut Cfg, context: &mut SsaContext) {
   context.cur_block += 1;
   context.sealed.push(false);
   context.current_defs.push(HashMap::new());
   context.incomplete_phis.push(Vec::new());

   cfg.predecessors.push(Vec::new());
   cfg.successors.push(Vec::new());
}

impl SsaContext {
   fn write_variable(&mut self, var: StrId, value: usize, block: usize) {
      let variables_in_block = &mut self.current_defs[block];
      variables_in_block.insert(var, value);
   }

   fn read_variable(&mut self, var: StrId, block: usize, cfg: &Cfg) -> usize {
      if let Some(value) = self.current_defs[block].get(&var).copied() {
         return value;
      }

      self.read_variable_recursive(var, block, cfg)
   }

   fn read_variable_recursive(&mut self, var: StrId, block: usize, cfg: &Cfg) -> usize {
      let val = if !self.sealed[block] {
         // We don't know all of our predecessors yet, so we can't query them
         let new_phi = self.push_instruction(Instruction::Phi(Vec::new()));
         // We'll use this reference to come back later
         self.incomplete_phis[self.cur_block].push(new_phi);
         new_phi
      } else if cfg.predecessors[block].len() == 1 {
         self.read_variable(var, cfg.predecessors[block][0], cfg)
      } else {
         let new_phi = self.push_instruction(Instruction::Phi(Vec::new()));
         self.write_variable(var, new_phi, block);
         for pred in cfg.predecessors[block].iter().copied() {
            let variable_in_pred = self.read_variable(var, pred, cfg);
            self.values[new_phi].get_phi_operands().push(variable_in_pred);
         }
         // The resulting phi may be trivial, TODO
         new_phi
      };

      self.write_variable(var, val, block);
      val
   }

   fn push_instruction(&mut self, instruction: Instruction) -> usize {
      let len_before = self.values.len();
      self.values.push(instruction);
      len_before
   }
}

pub fn linearize<W: Write>(program: &mut Program, err_stream: &mut W) {
   let mut ssa_procedures: HashMap<StrId, SsaContext> = HashMap::new();
   for procedure in program.procedures.iter_mut() {
      let mut cfg = Cfg {
         predecessors: Vec::new(),
         successors: Vec::new(),
      };

      let mut context = SsaContext {
         sealed: Vec::new(),
         values: Vec::new(),
         current_defs: Vec::new(),
         incomplete_phis: Vec::new(),
         cur_block: 0,
      };

      // BB0
      new_basic_block(&mut cfg, &mut context);
      // The first basic block can't have any predecessors
      *context.sealed.first_mut().unwrap() = true;
      context.cur_block = 0;

      lower_ast_block(&mut procedure.block, err_stream, &mut context, &mut cfg);
   }
}

fn lower_ast_block<W: Write>(
   block: &mut BlockNode,
   err_stream: &mut W,
   context: &mut SsaContext,
   cfg: &mut Cfg,
) {
   for statement in block.statements.iter_mut() {
      lower_ast_statement(&mut statement.statement, err_stream, context, cfg);
   }
}

fn lower_ast_statement<W: Write>(
   statement: &mut Statement,
   err_stream: &mut W,
   context: &mut SsaContext,
   cfg: &mut Cfg,
) {
   match statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         if let Expression::Variable(id) = lhs_expr.expression {
            let rhs = lower_ast_expr(rhs_expr, err_stream, context, cfg);
            context.write_variable(id, rhs, context.cur_block);
         } else {
            let _lhs = lower_ast_expr(lhs_expr, err_stream, context, cfg);
            let _rhs = lower_ast_expr(rhs_expr, err_stream, context, cfg);
            todo!()
         }
      }
      Statement::Block(block) => {
         lower_ast_block(block, err_stream, context, cfg);
      }
      Statement::Break => {
         todo!();
      },
      Statement::Continue => {
         todo!();
      },
      Statement::IfElse(if_expr, if_block, else_statement) => {
         let cond_on = lower_ast_expr(if_expr, err_stream, context, cfg);
         context.push_instruction(Instruction::Branch(cond_on, context.cur_block + 1));
         lower_ast_block(if_block, err_stream, context, cfg);
         lower_ast_statement(&mut else_statement.statement, err_stream, context, cfg);
      }
      Statement::For(_var, start_expr, end_expr, block, _) => {
         lower_ast_expr(start_expr, err_stream, context, cfg);
         lower_ast_expr(end_expr, err_stream, context, cfg);
         lower_ast_block(block, err_stream, context, cfg);
      }
      Statement::Loop(block) => {
         lower_ast_block(block, err_stream, context, cfg);
      }
      Statement::Expression(expr) => {
         lower_ast_expr(expr, err_stream, context, cfg);
      }
      Statement::Return(expr) => {
         lower_ast_expr(expr, err_stream, context, cfg);
      }
      Statement::VariableDeclaration(id, expr, _) => {
         let value = lower_ast_expr(expr, err_stream, context, cfg);
         context.write_variable(id.identifier, value, context.cur_block);
      }
   }
}

#[must_use]
fn lower_ast_expr<W: Write>(
   expr_to_lower: &mut ExpressionNode,
   err_stream: &mut W,
   context: &mut SsaContext,
   cfg: &mut Cfg,
) -> usize {
   match &mut expr_to_lower.expression {
      Expression::ArrayIndex(array, index) => {
         lower_ast_expr(array, err_stream, context, cfg);
         lower_ast_expr(index, err_stream, context, cfg);
         todo!()
      }
      Expression::Variable(x) => {
         context.read_variable(*x, context.cur_block, cfg)
      },
      Expression::ProcedureCall(_name, args) => {
         for arg in args.iter_mut() {
            lower_ast_expr(&mut arg.expr, err_stream, context, cfg);
         }
         todo!()
      }
      Expression::ArrayLiteral(_) => todo!(),
      Expression::BoolLiteral(_) => todo!(),
      Expression::StringLiteral(_) => todo!(),
      Expression::IntLiteral(x) => {
         context.push_instruction(Instruction::IntLiteral(*x))
      },
      Expression::FloatLiteral(_) => todo!(),
      Expression::UnitLiteral => todo!(),
      Expression::EnumLiteral(_, _) => todo!(),
      Expression::BinaryOperator(opcode, exprs) => {
         let lhs = lower_ast_expr(&mut exprs.0, err_stream, context, cfg);
         let rhs = lower_ast_expr(&mut exprs.1, err_stream, context, cfg);
         context.push_instruction(Instruction::BinaryExpression(*opcode, lhs, rhs))
      }
      Expression::UnaryOperator(opcode, expr) => {
         let inner = lower_ast_expr(expr, err_stream, context, cfg);
         context.push_instruction(Instruction::UnaryExpression(*opcode, inner))
      }
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter_mut() {
            lower_ast_expr(expr, err_stream, context, cfg);
         }
         todo!()
      }
      Expression::FieldAccess(_, expr) => {
         lower_ast_expr(expr, err_stream, context, cfg);
         todo!()
      }
      Expression::Extend(_, expr) => {
         lower_ast_expr(expr, err_stream, context, cfg);
         todo!()
      }
      Expression::Truncate(_, expr) => {
         lower_ast_expr(expr, err_stream, context, cfg);
         todo!()
      }
      Expression::Transmute(_, expr) => {
         lower_ast_expr(expr, err_stream, context, cfg);
         todo!()
      }
   }
}
