use std::borrow::Cow;
use std::io::Write;

use arrayvec::ArrayVec;
use indexmap::IndexMap;

use super::linearize::{Cfg, CfgInstruction, CFG_END_NODE, CFG_START_NODE};
use super::regalloc;
use crate::interner::Interner;
use crate::type_data::{ExpressionType, IntType, IntWidth, F32_TYPE, F64_TYPE};
use crate::{CompilationConfig, Program};
use crate::parse::{AstPool, CastType, Expression, ExpressionId, VariableId};

struct GenerationContext<'a> {
   buf: Vec<u8>,
   is_main: bool,
   var_to_reg: IndexMap<VariableId, ArrayVec<u32, 1>>,
   ast: &'a AstPool,
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

pub fn emit_qbe(program: &mut Program, interner: &mut Interner, config: &CompilationConfig) -> Vec<u8> {
   let regalloc_result = regalloc::assign_variables_to_wasm_registers(program, config);

   let mut ctx = GenerationContext {
      buf: vec![],
      is_main: false,
      var_to_reg: regalloc_result.var_to_reg,
      ast: &program.ast,
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
      writeln!(
         ctx.buf,
         "{}function {} ${}() {{",
         export_txt,
         abi_ret_type,
         interner.lookup(procedure.definition.name.str)
      )
      .unwrap();
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
         CfgInstruction::Assignment(len, en) => {
            /*
            do_emit(*len, generation_context);
            do_emit_and_load_lval(*en, generation_context);
            let val_type = generation_context.ast.expressions[*en].exp_type.as_ref().unwrap();
            if let Some((is_global, range)) = get_registers_for_expr(*len, generation_context) {
               if is_global {
                  for a_reg in range.iter().rev() {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::GlobalSet(*a_reg));
                  }
               } else {
                  for a_reg in range.iter().rev() {
                     generation_context
                        .active_fcn
                        .instruction(&Instruction::LocalSet(*a_reg));
                  }
               }
            } else {
               store_mem(val_type, generation_context);
            } */
            todo!();
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
            do_emit(*en, ctx);
         }
         CfgInstruction::Return(en) => {
            /*
            do_emit_and_load_lval(*en, generation_context);

            if generation_context.ast.expressions[*en]
               .exp_type
               .as_ref()
               .unwrap()
               .is_never()
            {
               // We have already emitted a literal "unreachable", no need to adjust the stack
            } else {
               adjust_stack_function_exit(generation_context);
               generation_context.active_fcn.instruction(&Instruction::Return);
            }
            */
            //todo!();
            if ctx.is_main {
               // World's biggest hack
               writeln!(&mut ctx.buf, "   ret 0").unwrap();
            } else {
               writeln!(&mut ctx.buf, "   ret").unwrap();
            }
         }
         CfgInstruction::Jump(dest) => {
            if *dest != CFG_END_NODE {
               writeln!(&mut ctx.buf, "   jmp @b{}", dest).unwrap();
            }
         }
         CfgInstruction::ConditionalJump(expr, then_dest, else_dest) => {
            writeln!(&mut ctx.buf, "   jnz @b{} b@{}", then_dest, else_dest).unwrap();
         },
      }
   }
}

// TODO: rework this to write directly into bytestream or otherwise not allocate
fn expr_as_val(expr_index: ExpressionId, ctx: &mut GenerationContext) -> String {
   let expr_node = &ctx.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::IntLiteral { val, .. } => todo!(),
      Expression::FloatLiteral(v) => match expr_node.exp_type.as_ref().unwrap() {
         &F64_TYPE => format!("d_{}", v),
         &F32_TYPE => format!("s_{}", v),
         _ => unreachable!(),
      },
      Expression::BoolLiteral(_) => todo!(),
      Expression::Variable(_) => todo!(),
      _ => unreachable!(),
   }
}

fn do_emit(expr_index: ExpressionId, ctx: &mut GenerationContext) {
   let expr_node = &ctx.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::IfX(a, b, c) => todo!(),
      Expression::BoolLiteral(_) | Expression::IntLiteral { .. } | Expression::Variable(_) | Expression::FloatLiteral(_) | Expression::StringLiteral(_)
      | Expression::BoundFcnLiteral(_, _) | Expression::UnitLiteral => {
         // top level literal. must have no side effect. skip
      },
      Expression::BinaryOperator { operator, lhs, rhs } => todo!(),
      Expression::UnaryOperator(un_op, e_index) => todo!(),
      Expression::Cast {
         cast_type: CastType::Transmute,
         expr: e_id,
         ..
      } => todo!(),
      Expression::Cast {
         cast_type: CastType::As,
         expr: e,
         ..
      } => todo!(),
      Expression::ProcedureCall { proc_expr, args } => todo!(),
      Expression::StructLiteral(s_id, fields) => todo!(),
      Expression::FieldAccess(field_name, lhs_id) => todo!(),
      Expression::ArrayLiteral(exprs) => todo!(),
      Expression::ArrayIndex { array, index } => todo!(),
      Expression::EnumLiteral(_, _) => unreachable!(),
      Expression::UnresolvedVariable(_) | Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::UnresolvedStructLiteral(_, _) | Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
   }
   if expr_node.exp_type.as_ref().unwrap().is_never() {
      writeln!(&mut ctx.buf, "   hlt").unwrap();
   }
}
