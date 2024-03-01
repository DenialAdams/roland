use std::io::Write;

use arrayvec::ArrayVec;
use indexmap::IndexMap;
use slotmap::SecondaryMap;

use super::linearize::{Cfg, CfgInstruction, CFG_END_NODE, CFG_START_NODE};
use super::regalloc;
use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::Interner;
use crate::parse::{AstPool, Expression, ExpressionId, ProcedureId, VariableId};
use crate::semantic_analysis::ProcedureInfo;
use crate::type_data::{ExpressionType, IntType, IntWidth, F32_TYPE, F64_TYPE};
use crate::{CompilationConfig, Program};

struct GenerationContext<'a> {
   buf: Vec<u8>,
   is_main: bool,
   var_to_reg: IndexMap<VariableId, ArrayVec<u32, 1>>,
   ast: &'a AstPool,
   proc_info: &'a SecondaryMap<ProcedureId, ProcedureInfo>,
   interner: &'a Interner,
}

fn roland_type_to_base_type(r_type: &ExpressionType) -> &'static str {
   match r_type {
      ExpressionType::Bool => "w",
      &F32_TYPE => "s",
      &F64_TYPE => "d",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Eight,
      }) => "l",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Four | IntWidth::Two | IntWidth::One,
      }) => "w",
      ExpressionType::Unit => "",
      _ => todo!(),
   }
}

fn roland_type_to_abi_type(r_type: &ExpressionType) -> &'static str {
   match r_type {
      ExpressionType::Bool => "ub",
      &F32_TYPE => "s",
      &F64_TYPE => "d",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Eight,
      }) => "l",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Four,
      }) => "w",
      ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::Two,
      }) => "sh",
      ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::Two,
      }) => "uh",
      ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::One,
      }) => "sb",
      ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::One,
      }) => "ub",
      ExpressionType::Unit => "",
      _ => todo!(),
   }
}

pub fn emit_qbe(program: &mut Program, interner: &Interner, config: &CompilationConfig) -> Vec<u8> {
   let regalloc_result = regalloc::assign_variables_to_wasm_registers(program, config);

   let mut ctx = GenerationContext {
      buf: vec![],
      is_main: false,
      var_to_reg: regalloc_result.var_to_reg,
      ast: &program.ast,
      proc_info: &program.procedure_info,
      interner,
   };

   for (proc_id, procedure) in program.procedures.iter() {
      let Some(cfg) = program.cfg.get(proc_id) else {
         continue;
      };

      let export_txt = if interner.lookup(procedure.definition.name.str) == "main" {
         ctx.is_main = true;
         "export "
      } else {
         ctx.is_main = false;
         ""
      };
      let abi_ret_type = if ctx.is_main {
         "w"
      } else {
         roland_type_to_abi_type(&procedure.definition.ret_type.e_type)
      };
      write!(
         ctx.buf,
         "{}function {} ${}(",
         export_txt,
         abi_ret_type,
         interner.lookup(procedure.definition.name.str)
      )
      .unwrap();
      for (i, param) in procedure.definition.parameters.iter().enumerate() {
         let param_reg = ctx.var_to_reg.get(&param.var_id).unwrap()[0];
         if i == procedure.definition.parameters.len() - 1 {
            write!(
               ctx.buf,
               "{} %v{}",
               roland_type_to_abi_type(&param.p_type.e_type),
               param_reg
            )
            .unwrap();
         } else {
            write!(
               ctx.buf,
               "{} %v{}, ",
               roland_type_to_abi_type(&param.p_type.e_type),
               param_reg
            )
            .unwrap();
         }
      }
      writeln!(ctx.buf, ") {{").unwrap();
      emit_bb(cfg, CFG_START_NODE, &mut ctx);
      for bb_id in 2..cfg.bbs.len() {
         emit_bb(cfg, bb_id, &mut ctx);
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   ctx.buf
}

fn emit_bb(cfg: &Cfg, bb: usize, ctx: &mut GenerationContext) {
   writeln!(ctx.buf, "@b{}", bb).unwrap();
   for instr in cfg.bbs[bb].instructions.iter() {
      match instr {
         CfgInstruction::IfElse(_, _, _, _) => (),
         CfgInstruction::Break => (),
         CfgInstruction::Continue => (),
         CfgInstruction::Loop(_, _) => (),
         CfgInstruction::Assignment(lid, en) => {
            let len = &ctx.ast.expressions[*lid];
            match len.expression {
               Expression::Variable(v) => {
                  let reg = ctx.var_to_reg.get(&v).unwrap()[0];
                  write!(
                     ctx.buf,
                     "   %v{} ={} ",
                     reg,
                     roland_type_to_base_type(len.exp_type.as_ref().unwrap())
                  )
                  .unwrap();
               }
               _ => unreachable!(),
            };
            let ren = &ctx.ast.expressions[*en];
            match &ren.expression {
               Expression::ProcedureCall { proc_expr, args } => {
                  let callee = match ctx.ast.expressions[*proc_expr].exp_type.as_ref().unwrap() {
                     ExpressionType::ProcedureItem(id, _) => ctx.interner.lookup(ctx.proc_info[*id].name.str),
                     ExpressionType::ProcedurePointer { .. } => todo!(),
                     _ => unreachable!(),
                  };
                  write!(ctx.buf, "call ${}(", callee).unwrap();
                  for (i, arg) in args.iter().enumerate() {
                     let val = expr_to_val(arg.expr, ctx);
                     if i == args.len() - 1 {
                        write!(
                           ctx.buf,
                           "{} {}",
                           roland_type_to_abi_type(ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap()),
                           val
                        )
                        .unwrap();
                     } else {
                        write!(
                           ctx.buf,
                           "{} {}, ",
                           roland_type_to_abi_type(ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap()),
                           val
                        )
                        .unwrap();
                     }
                  }
                  writeln!(ctx.buf, ")").unwrap();
               }
               Expression::ArrayLiteral(_) => todo!(),
               Expression::ArrayIndex { array, index } => todo!(),
               Expression::BoolLiteral(v) => {
                  writeln!(ctx.buf, "copy {}", *v as u8).unwrap();
               }
               Expression::StringLiteral(_) => todo!(),
               Expression::IntLiteral { val, .. } => {
                  // TODO: print with negative?
                  writeln!(ctx.buf, "copy {}", val).unwrap();
               }
               Expression::FloatLiteral(val) => match ren.exp_type.as_ref().unwrap() {
                  &F64_TYPE => writeln!(ctx.buf, "copy d_{}", val).unwrap(),
                  &F32_TYPE => writeln!(ctx.buf, "copy s_{}", val).unwrap(),
                  _ => unreachable!(),
               },
               Expression::UnitLiteral => todo!(),
               Expression::UnresolvedVariable(_) => todo!(),
               Expression::Variable(v) => {
                  let reg = ctx.var_to_reg.get(v).unwrap();
                  writeln!(ctx.buf, "copy %v{}", reg[0]).unwrap();
               }
               Expression::BinaryOperator { operator, lhs, rhs } => {
                  let opcode = match operator {
                     crate::parse::BinOp::Add => "add",
                     crate::parse::BinOp::Subtract => "sub",
                     crate::parse::BinOp::Multiply => "mul",
                     crate::parse::BinOp::Divide => todo!(),
                     crate::parse::BinOp::Remainder => todo!(),
                     crate::parse::BinOp::Equality => "eq",
                     crate::parse::BinOp::NotEquality => "ne",
                     crate::parse::BinOp::GreaterThan => todo!(),
                     crate::parse::BinOp::LessThan => todo!(),
                     crate::parse::BinOp::GreaterThanOrEqualTo => todo!(),
                     crate::parse::BinOp::LessThanOrEqualTo => todo!(),
                     crate::parse::BinOp::BitwiseAnd => "and",
                     crate::parse::BinOp::BitwiseOr => "or",
                     crate::parse::BinOp::BitwiseXor => "xor",
                     crate::parse::BinOp::BitwiseLeftShift => "shl",
                     crate::parse::BinOp::BitwiseRightShift => todo!(),
                     crate::parse::BinOp::LogicalAnd => unreachable!(),
                     crate::parse::BinOp::LogicalOr => unreachable!(),
                  };
                  let lhs_val = expr_to_val(*lhs, ctx);
                  let rhs_val = expr_to_val(*rhs, ctx);
                  writeln!(ctx.buf, "{} {}, {}", opcode, lhs_val, rhs_val).unwrap();
               }
               Expression::UnaryOperator(operator, inner_id) => {
                  let inner_val = expr_to_val(*inner_id, ctx);
                  match operator {
                     crate::parse::UnOp::Negate => writeln!(ctx.buf, "neg {}", inner_val).unwrap(),
                     crate::parse::UnOp::Complement => {
                        if *ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap() == ExpressionType::Bool {
                           writeln!(ctx.buf, "eq {}, 0", inner_val).unwrap()
                        } else {
                           let magic_const: u64 = match *ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap() {
                              crate::type_data::U8_TYPE => u64::from(std::u8::MAX),
                              crate::type_data::U16_TYPE => u64::from(std::u16::MAX),
                              crate::type_data::U32_TYPE => u64::from(std::u32::MAX),
                              crate::type_data::U64_TYPE => std::u64::MAX,
                              crate::type_data::I8_TYPE => u64::from(std::u32::MAX),
                              crate::type_data::I16_TYPE => u64::from(std::u32::MAX),
                              crate::type_data::I32_TYPE => u64::from(std::u32::MAX),
                              crate::type_data::I64_TYPE => std::u64::MAX,
                              _ => unreachable!(),
                           };
                           writeln!(ctx.buf, "xor {}, {}", inner_val, magic_const).unwrap()
                        }
                     }
                     crate::parse::UnOp::AddressOf => todo!(),
                     crate::parse::UnOp::Dereference => todo!(),
                  }
               }
               Expression::UnresolvedStructLiteral(_, _) => todo!(),
               Expression::StructLiteral(_, _) => todo!(),
               Expression::FieldAccess(_, _) => todo!(),
               Expression::Cast {
                  cast_type,
                  target_type,
                  expr,
               } => todo!(),
               Expression::EnumLiteral(_, _) => todo!(),
               Expression::UnresolvedEnumLiteral(_, _) => todo!(),
               Expression::UnresolvedProcLiteral(_, _) => todo!(),
               Expression::BoundFcnLiteral(_, _) => todo!(),
               Expression::IfX(_, _, _) => todo!(),
            }
         }
         CfgInstruction::Expression(en) => match &ctx.ast.expressions[*en].expression {
            Expression::ProcedureCall { proc_expr, args } => todo!(),
            _ => debug_assert!(!expression_could_have_side_effects(*en, &ctx.ast.expressions)),
         },
         CfgInstruction::Return(en) => {
            if ctx.is_main {
               // World's biggest hack
               writeln!(&mut ctx.buf, "   ret 0").unwrap();
            } else {
               if *ctx.ast.expressions[*en].exp_type.as_ref().unwrap() != ExpressionType::Unit {
                  let val = expr_to_val(*en, ctx);
                  writeln!(&mut ctx.buf, "   ret {}", val).unwrap();
               } else {
                  writeln!(&mut ctx.buf, "   ret").unwrap();
               }
            }
         }
         CfgInstruction::Jump(dest) => {
            if *dest != CFG_END_NODE {
               writeln!(&mut ctx.buf, "   jmp @b{}", dest).unwrap();
            }
         }
         CfgInstruction::ConditionalJump(expr, then_dest, else_dest) => {
            writeln!(&mut ctx.buf, "   jnz @b{} b@{}", then_dest, else_dest).unwrap();
         }
      }
   }
}

// TODO: rework this to write directly into bytestream or otherwise not allocate
fn expr_to_val(expr_index: ExpressionId, ctx: &mut GenerationContext) -> String {
   let expr_node = &ctx.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::IntLiteral { val, .. } => {
         format!("{}", *val)
      }
      Expression::FloatLiteral(v) => match expr_node.exp_type.as_ref().unwrap() {
         &F64_TYPE => format!("d_{}", v),
         &F32_TYPE => format!("s_{}", v),
         _ => unreachable!(),
      },
      Expression::BoolLiteral(val) => {
         format!("{}", *val as u8)
      }
      Expression::Variable(v) => {
         format!("%v{}", ctx.var_to_reg.get(v).unwrap()[0])
      }
      _ => unreachable!(),
   }
}
