use std::io::Write;

use arrayvec::ArrayVec;
use indexmap::IndexMap;
use slotmap::SecondaryMap;

use super::linearize::{Cfg, CfgInstruction, CFG_END_NODE, CFG_START_NODE};
use super::regalloc;
use crate::interner::Interner;
use crate::parse::{AstPool, Expression, ProcedureId, VariableId};
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
      ).unwrap();
      for (i, param) in procedure.definition.parameters.iter().enumerate() {
         let param_reg = ctx.var_to_reg.get(&param.var_id).unwrap()[0];
         if i == procedure.definition.parameters.len() - 1 {
            write!(ctx.buf, "{} %v{}", roland_type_to_abi_type(&param.p_type.e_type), param_reg).unwrap();
         } else {
            write!(ctx.buf, "{} %v{}, ", roland_type_to_abi_type(&param.p_type.e_type), param_reg).unwrap();
         }
      }
      writeln!(
         ctx.buf,
         ") {{"
      ).unwrap();
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
                  let reg = ctx.var_to_reg.get(&v).unwrap();
                  write!(
                     ctx.buf,
                     "   %v{} ={} ",
                     reg[0],
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
                     ExpressionType::ProcedureItem(id, _) => {
                        ctx.interner.lookup(ctx.proc_info[*id].name.str)
                     }
                     ExpressionType::ProcedurePointer { .. } => todo!(),
                     _ => unreachable!(),
                  };
                  write!(ctx.buf, "call ${}(", callee).unwrap();
                  for (i, arg) in args.iter().enumerate() {
                     let Expression::Variable(inner_v) = ctx.ast.expressions[arg.expr].expression else {
                        unreachable!();
                     };
                     let inner = ctx.var_to_reg.get(&inner_v).unwrap()[0];
                     if i == args.len() - 1 {
                        write!(ctx.buf, "{} %v{}", roland_type_to_abi_type(ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap()), inner).unwrap();
                     } else {
                        write!(ctx.buf, "{} %v{}, ", roland_type_to_abi_type(ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap()), inner).unwrap();
                     }
                  }
                  writeln!(ctx.buf, ")").unwrap();
               },
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
               Expression::BinaryOperator { operator, lhs, rhs } =>
               { 
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
                  let Expression::Variable(lhs_v) = ctx.ast.expressions[*lhs].expression else {
                     unreachable!();
                  };
                  let Expression::Variable(rhs_v) = ctx.ast.expressions[*rhs].expression else {
                     unreachable!();
                  };
                  let lhs = ctx.var_to_reg.get(&lhs_v).unwrap()[0];
                  let rhs = ctx.var_to_reg.get(&rhs_v).unwrap()[0];
                  writeln!(ctx.buf, "{} %v{}, %v{}", opcode, lhs, rhs).unwrap();
               },
               Expression::UnaryOperator(operator, inner_id) => {
                  let Expression::Variable(inner_v) = ctx.ast.expressions[*inner_id].expression else {
                     unreachable!();
                  };
                  let inner = ctx.var_to_reg.get(&inner_v).unwrap()[0];
                  match operator {
                    crate::parse::UnOp::Negate => writeln!(ctx.buf, "neg %v{}", inner).unwrap(),
                    crate::parse::UnOp::Complement => if *ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap() == ExpressionType::Bool {
                     writeln!(ctx.buf, "eq %v{}, 0", inner).unwrap()
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
                     writeln!(ctx.buf, "xor %v{}, {}", inner, magic_const).unwrap()
                    },
                    crate::parse::UnOp::AddressOf => todo!(),
                    crate::parse::UnOp::Dereference => todo!(),
                  }
               },
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
         CfgInstruction::Expression(en) => {
            /*
            do_emit_and_load_lval(*en, generation_context);
            for _ in 0..sizeof_type_values(
               generation_context.ast.expressions[*en].exp_type.as_ref().unwrap(),
               &generation_context.user_defined_types.enum_info,
               &generation_context.user_defined_types.struct_info,
            ) {
               generation_context.active_fcn.instruction(&Instruction::Drop);
            } */
            ()
         }
         CfgInstruction::Return(en) => {
            if ctx.is_main {
               // World's biggest hack
               writeln!(&mut ctx.buf, "   ret 0").unwrap();
            } else {
               if *ctx.ast.expressions[*en].exp_type.as_ref().unwrap() != ExpressionType::Unit {
                  let Expression::Variable(inner_v) = ctx.ast.expressions[*en].expression else {
                     unreachable!();
                  };
                  let inner = ctx.var_to_reg.get(&inner_v).unwrap()[0];
                  writeln!(&mut ctx.buf, "   ret %v{}", inner).unwrap();
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
