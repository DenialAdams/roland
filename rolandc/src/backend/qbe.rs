use std::io::Write;

use indexmap::{IndexMap, IndexSet};
use slotmap::SecondaryMap;

use super::linearize::{Cfg, CfgInstruction, CFG_END_NODE, CFG_START_NODE};
use super::regalloc;
use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::{Interner, StrId};
use crate::parse::{
   ArgumentNode, AstPool, CastType, Expression, ExpressionId, ProcedureId, UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::ProcedureInfo;
use crate::size_info::{mem_alignment, sizeof_type_mem};
use crate::type_data::{
   ExpressionType, IntType, IntWidth, F32_TYPE, F64_TYPE, I16_TYPE, I32_TYPE, I64_TYPE, I8_TYPE, U16_TYPE, U32_TYPE,
   U64_TYPE, U8_TYPE,
};
use crate::{CompilationConfig, Program, Target};

struct GenerationContext<'a> {
   buf: Vec<u8>,
   is_main: bool,
   var_to_reg: IndexMap<VariableId, u32>,
   ast: &'a AstPool,
   proc_info: &'a SecondaryMap<ProcedureId, ProcedureInfo>,
   interner: &'a Interner,
   udt: &'a UserDefinedTypeInfo,
   string_literals: &'a IndexSet<StrId>,
   address_temp: u64,
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

fn roland_type_to_extended_type(r_type: &ExpressionType) -> &'static str {
   match r_type {
      ExpressionType::Bool => "b",
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
         signed: _,
         width: IntWidth::Two,
      }) => "h",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::One,
      }) => "b",
      x => unreachable!("{:?}", x),
   }
}

fn roland_type_to_abi_type(r_type: &ExpressionType, udt: &UserDefinedTypeInfo, interner: &Interner) -> String {
   match r_type {
      ExpressionType::Bool => "ub".into(),
      &F32_TYPE => "s".into(),
      &F64_TYPE => "d".into(),
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Eight,
      }) => "l".into(),
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Four,
      }) => "w".into(),
      ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::Two,
      }) => "sh".into(),
      ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::Two,
      }) => "uh".into(),
      ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::One,
      }) => "sb".into(),
      ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::One,
      }) => "ub".into(),
      ExpressionType::Unit => "".into(), // TODO
      ExpressionType::Struct(sid) => {
         format!(":{}", interner.lookup(udt.struct_info.get(*sid).unwrap().name))
      }
      _ => todo!(),
   }
}

// TODO: we'll make this not alloc
fn roland_type_to_sub_type(r_type: &ExpressionType, udt: &UserDefinedTypeInfo, interner: &Interner) -> String {
   match r_type {
      ExpressionType::Bool => "b".into(),
      &F32_TYPE => "s".into(),
      &F64_TYPE => "d".into(),
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Eight,
      }) => "l".into(),
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Four,
      }) => "w".into(),
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Two,
      }) => "h".into(),
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::One,
      }) => "b".into(),
      ExpressionType::Struct(sid) => {
         format!(":{}", interner.lookup(udt.struct_info.get(*sid).unwrap().name))
      }
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
      udt: &program.user_defined_types,
      string_literals: &program.literals,
      address_temp: 0,
   };

   for (i, string_literal) in ctx.string_literals.iter().enumerate() {
      let str = ctx.interner.lookup(*string_literal);
      if str.chars().all(|x| !x.is_ascii_control() && x.is_ascii()) {
         writeln!(
            ctx.buf,
            "data $s{} = {{ b \"{}\" }}",
            i,
            ctx.interner.lookup(*string_literal)
         )
         .unwrap();
      } else {
         write!(ctx.buf, "data $s{} = {{ b ", i).unwrap();
         for by in str.as_bytes() {
            write!(ctx.buf, "{} ", by).unwrap();
         }
         writeln!(ctx.buf, "}}").unwrap();
      }
   }

   for a_struct in program.user_defined_types.struct_info.iter() {
      write!(ctx.buf, "type :{} = {{ ", ctx.interner.lookup(a_struct.1.name)).unwrap();
      for (i, field_type) in a_struct.1.field_types.values().map(|x| &x.e_type).enumerate() {
         if i == a_struct.1.field_types.len() - 1 {
            write!(
               ctx.buf,
               "{}",
               roland_type_to_sub_type(field_type, ctx.udt, ctx.interner)
            )
            .unwrap();
         } else {
            write!(
               ctx.buf,
               "{}, ",
               roland_type_to_sub_type(field_type, ctx.udt, ctx.interner)
            )
            .unwrap();
         }
      }
      writeln!(ctx.buf, " }}").unwrap();
   }

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
         "w".into()
      } else {
         roland_type_to_abi_type(&procedure.definition.ret_type.e_type, ctx.udt, ctx.interner)
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
         if let Some(param_reg) = ctx.var_to_reg.get(&param.var_id) {
            write!(
               ctx.buf,
               "{} %r{}",
               roland_type_to_abi_type(&param.p_type.e_type, ctx.udt, ctx.interner),
               param_reg
            )
            .unwrap();
         } else {
            write!(
               ctx.buf,
               "{} %p{}",
               roland_type_to_abi_type(&param.p_type.e_type, ctx.udt, ctx.interner),
               param.var_id.0,
            )
            .unwrap();
            // Need to emit a copy
         }

         if i != procedure.definition.parameters.len() - 1 {
            write!(ctx.buf, ", ").unwrap();
         }
      }
      writeln!(ctx.buf, ") {{").unwrap();
      // Allocate stack
      writeln!(ctx.buf, "@entry").unwrap();
      for local in procedure.locals.iter() {
         if ctx.var_to_reg.contains_key(local.0) {
            continue;
         }
         if sizeof_type_mem(local.1, ctx.udt, Target::Qbe) == 0 {
            continue;
         }
         let alignment = {
            let align_floor_4 = mem_alignment(local.1, ctx.udt, Target::Qbe).max(4);
            if align_floor_4 > 4 && align_floor_4 <= 8 {
               8
            } else if align_floor_4 > 4 {
               16
            } else {
               align_floor_4
            }
         };
         writeln!(
            ctx.buf,
            "   %v{} =l alloc{} {}",
            local.0 .0,
            alignment,
            sizeof_type_mem(local.1, ctx.udt, Target::Qbe),
         )
         .unwrap();
      }
      // Copy mem parameters
      for param in procedure.definition.parameters.iter() {
         if ctx.var_to_reg.contains_key(&param.var_id) {
            continue;
         }
         let size = sizeof_type_mem(&param.p_type.e_type, ctx.udt, Target::Qbe);
         writeln!(ctx.buf, "   blit %p{}, %v{}, {}", param.var_id.0, param.var_id.0, size).unwrap();
      }
      emit_bb(cfg, CFG_START_NODE, &mut ctx);
      for bb_id in 2..cfg.bbs.len() {
         emit_bb(cfg, bb_id, &mut ctx);
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   ctx.buf
}

fn compute_offset(expr: ExpressionId, ctx: &mut GenerationContext) -> Option<String> {
   match ctx.ast.expressions[expr].expression {
      Expression::FieldAccess(field, base) => {
         let base_mem = compute_offset(base, ctx).unwrap();
         match ctx.ast.expressions[base].exp_type.as_ref().unwrap() {
            ExpressionType::Struct(sid) => {
               let offset = ctx
                  .udt
                  .struct_info
                  .get(*sid)
                  .unwrap()
                  .size
                  .as_ref()
                  .unwrap()
                  .field_offsets_mem
                  .get(&field)
                  .unwrap();
               if *offset == 0 {
                  return Some(base_mem);
               }
               let at = ctx.address_temp;
               ctx.address_temp += 1;
               writeln!(ctx.buf, "   %a{} =l add {}, {}", at, base_mem, offset).unwrap();
               Some(format!("%a{}", at))
            }
            ExpressionType::Union(_) => Some(base_mem),
            _ => unreachable!(),
         }
      }
      Expression::ArrayIndex { array, index } => {
         let base_mem = compute_offset(array, ctx).unwrap();
         let sizeof_inner = match &ctx.ast.expressions[array].exp_type {
            Some(ExpressionType::Array(x, _)) => sizeof_type_mem(x, ctx.udt, Target::Qbe),
            _ => unreachable!(),
         };

         let index_val = expr_to_val(index, ctx);

         writeln!(ctx.buf, "   %t =l mul {}, {}", sizeof_inner, index_val).unwrap();
         let at = ctx.address_temp;
         ctx.address_temp += 1;
         writeln!(ctx.buf, "   %a{} =l add {}, %t", at, base_mem).unwrap();
         Some(format!("%a{}", at))
      }
      Expression::Variable(v) => {
         if ctx.var_to_reg.contains_key(&v) {
            None
         } else {
            Some(format!("%v{}", v.0))
         }
      }
      _ => None,
   }
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
            let lhs_mem = compute_offset(*lid, ctx);
            let rhs_mem = compute_offset(*en, ctx);
            match (&lhs_mem, &rhs_mem) {
               (Some(l), Some(r)) => {
                  let size = sizeof_type_mem(
                     ctx.ast.expressions[*lid].exp_type.as_ref().unwrap(),
                     ctx.udt,
                     Target::Qbe,
                  );
                  writeln!(ctx.buf, "   blit {}, {}, {}", r, l, size).unwrap();
                  continue;
               }
               (Some(l), None) => {
                  if ctx.ast.expressions[*lid].exp_type.as_ref().unwrap().is_aggregate() {
                     write!(
                        ctx.buf,
                        "   %t ={} ",
                        roland_type_to_abi_type(
                           ctx.ast.expressions[*lid].exp_type.as_ref().unwrap(),
                           ctx.udt,
                           ctx.interner
                        )
                     )
                     .unwrap();
                     write_expr(*en, rhs_mem, ctx);
                     let size = sizeof_type_mem(
                        ctx.ast.expressions[*lid].exp_type.as_ref().unwrap(),
                        ctx.udt,
                        Target::Qbe,
                     );
                     writeln!(ctx.buf, "   blit %t, {}, {}", l, size).unwrap();
                     continue;
                  }
                  let suffix = roland_type_to_extended_type(ctx.ast.expressions[*lid].exp_type.as_ref().unwrap());
                  let val = expr_to_val(*en, ctx);
                  writeln!(ctx.buf, "   store{} {}, {}", suffix, val, l).unwrap();
                  continue;
               }
               _ => (),
            }
            let len = &ctx.ast.expressions[*lid];
            match len.expression {
               Expression::Variable(v) => {
                  let reg = ctx.var_to_reg.get(&v).unwrap();
                  write!(
                     ctx.buf,
                     "   %r{} ={} ",
                     reg,
                     roland_type_to_base_type(len.exp_type.as_ref().unwrap())
                  )
                  .unwrap();
               }
               _ => unreachable!(),
            };
            write_expr(*en, rhs_mem, ctx);
         }
         CfgInstruction::Expression(en) => match &ctx.ast.expressions[*en].expression {
            Expression::ProcedureCall { proc_expr, args } => {
               write!(ctx.buf, "   ").unwrap();
               write_call_expr(*proc_expr, args, ctx);
            }
            _ => debug_assert!(!expression_could_have_side_effects(*en, &ctx.ast.expressions)),
         },
         CfgInstruction::Return(en) => {
            if ctx.is_main {
               // World's biggest hack
               writeln!(&mut ctx.buf, "   ret 0").unwrap();
            } else {
               // this whole thing is pretty suspect?
               if false && *ctx.ast.expressions[*en].exp_type.as_ref().unwrap() == ExpressionType::Never {
                  writeln!(&mut ctx.buf, "   halt").unwrap();
               } else if *ctx.ast.expressions[*en].exp_type.as_ref().unwrap() != ExpressionType::Unit {
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
            let cond = expr_to_val(*expr, ctx);
            writeln!(&mut ctx.buf, "   jnz {}, @b{}, @b{}", cond, then_dest, else_dest).unwrap();
         }
      }
   }
}

// TODO: rework this to write directly into bytestream or otherwise not allocate
fn expr_to_val(expr_index: ExpressionId, ctx: &mut GenerationContext) -> String {
   let expr_node = &ctx.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::IntLiteral { val, .. } => {
         let signed = matches!(
            expr_node.exp_type.as_ref().unwrap(),
            ExpressionType::Int(IntType { signed: true, .. })
         );
         if signed {
            format!("{}", *val as i64)
         } else {
            format!("{}", *val)
         }
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
         if let Some(reg) = ctx.var_to_reg.get(v) {
            format!("%r{}", reg)
         } else {
            format!("%v{}", v.0)
         }
      }
      Expression::StringLiteral(id) => {
         format!("$s{}", ctx.string_literals.get_index_of(id).unwrap())
      }
      x => unreachable!("{:?}", x),
   }
}

fn write_expr(expr: ExpressionId, rhs_mem: Option<String>, ctx: &mut GenerationContext) {
   let ren = &ctx.ast.expressions[expr];
   match &ren.expression {
      Expression::ProcedureCall { proc_expr, args } => {
         write_call_expr(*proc_expr, args, ctx);
      }
      Expression::BoolLiteral(v) => {
         writeln!(ctx.buf, "copy {}", *v as u8).unwrap();
      }
      Expression::StringLiteral(_) => todo!(),
      Expression::IntLiteral { val, .. } => {
         let signed = matches!(
            ren.exp_type.as_ref().unwrap(),
            ExpressionType::Int(IntType { signed: true, .. })
         );
         if signed {
            writeln!(ctx.buf, "copy {}", *val as i64).unwrap();
         } else {
            writeln!(ctx.buf, "copy {}", *val).unwrap();
         }
      }
      Expression::FloatLiteral(val) => match ren.exp_type.as_ref().unwrap() {
         &F64_TYPE => writeln!(ctx.buf, "copy d_{}", val).unwrap(),
         &F32_TYPE => writeln!(ctx.buf, "copy s_{}", val).unwrap(),
         _ => unreachable!(),
      },
      Expression::UnitLiteral => todo!(),
      Expression::UnresolvedVariable(_) => todo!(),
      Expression::Variable(v) => {
         if let Some(reg) = ctx.var_to_reg.get(v) {
            writeln!(ctx.buf, "copy %r{}", reg).unwrap();
         } else {
            match ren.exp_type.as_ref().unwrap() {
               ExpressionType::Bool | &U8_TYPE => {
                  writeln!(ctx.buf, "loadub %v{}", v.0).unwrap();
               }
               &I8_TYPE => {
                  writeln!(ctx.buf, "loadsb %v{}", v.0).unwrap();
               }
               &U16_TYPE => {
                  writeln!(ctx.buf, "loaduh %v{}", v.0).unwrap();
               }
               &I16_TYPE => {
                  writeln!(ctx.buf, "loadsh %v{}", v.0).unwrap();
               }
               &U32_TYPE => {
                  writeln!(ctx.buf, "loaduw %v{}", v.0).unwrap();
               }
               &I32_TYPE => {
                  writeln!(ctx.buf, "loadsw %v{}", v.0).unwrap();
               }
               &U64_TYPE | &I64_TYPE => {
                  writeln!(ctx.buf, "loadl %v{}", v.0).unwrap();
               }
               &F32_TYPE => {
                  writeln!(ctx.buf, "loads %v{}", v.0).unwrap();
               }
               &F64_TYPE => {
                  writeln!(ctx.buf, "loads %v{}", v.0).unwrap();
               }
               _ => unreachable!(),
            }
         }
      }
      Expression::BinaryOperator { operator, lhs, rhs } => {
         let typ = ctx.ast.expressions[*lhs].exp_type.as_ref().unwrap();
         let opcode = match operator {
            crate::parse::BinOp::Add => "add",
            crate::parse::BinOp::Subtract => "sub",
            crate::parse::BinOp::Multiply => "mul",
            crate::parse::BinOp::Divide => todo!(),
            crate::parse::BinOp::Remainder => todo!(),
            crate::parse::BinOp::Equality => match typ {
               ExpressionType::Bool => "ceqw",
               &F32_TYPE => "ceqs",
               &F64_TYPE => "ceqd",
               ExpressionType::Int(IntType {
                  signed: _,
                  width: IntWidth::Eight,
               }) => "ceql",
               ExpressionType::Int(IntType {
                  signed: _,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "ceqw",
               _ => unreachable!(),
            },
            crate::parse::BinOp::NotEquality => "ne",
            crate::parse::BinOp::GreaterThan => "gt",
            crate::parse::BinOp::LessThan => match typ {
               ExpressionType::Bool => "cultw",
               &F32_TYPE => "clts",
               &F64_TYPE => "cltd",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Eight,
               }) => "cultl",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "cultw",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Eight,
               }) => "csltl",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "csltw",
               _ => unreachable!(),
            },
            crate::parse::BinOp::GreaterThanOrEqualTo => match typ {
               ExpressionType::Bool => "cugew",
               &F32_TYPE => "cges",
               &F64_TYPE => "cged",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Eight,
               }) => "cugel",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "cugew",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Eight,
               }) => "csgel",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "csgew",
               _ => unreachable!(),
            },
            crate::parse::BinOp::LessThanOrEqualTo => "le",
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
      Expression::FieldAccess(_, _) | Expression::ArrayIndex { .. } => {
         let load_target = rhs_mem.unwrap();
         match ren.exp_type.as_ref().unwrap() {
            ExpressionType::Bool | &U8_TYPE => {
               writeln!(ctx.buf, "loadub {}", load_target).unwrap();
            }
            &I8_TYPE => {
               writeln!(ctx.buf, "loadsb {}", load_target).unwrap();
            }
            &U16_TYPE => {
               writeln!(ctx.buf, "loaduh {}", load_target).unwrap();
            }
            &I16_TYPE => {
               writeln!(ctx.buf, "loadsh {}", load_target).unwrap();
            }
            &U32_TYPE => {
               writeln!(ctx.buf, "loaduw {}", load_target).unwrap();
            }
            &I32_TYPE => {
               writeln!(ctx.buf, "loadsw {}", load_target).unwrap();
            }
            &U64_TYPE | &I64_TYPE => {
               writeln!(ctx.buf, "loadl {}", load_target).unwrap();
            }
            &F32_TYPE => {
               writeln!(ctx.buf, "loads {}", load_target).unwrap();
            }
            &F64_TYPE => {
               writeln!(ctx.buf, "loads {}", load_target).unwrap();
            }
            _ => unreachable!(),
         }
      }
      Expression::Cast {
         cast_type: CastType::As,
         target_type,
         expr,
      } => {
         writeln!(ctx.buf, "todoc").unwrap();
      }
      Expression::Cast {
         cast_type: CastType::Transmute,
         target_type,
         expr,
      } => {
         // hmm todo the variable could be a memory variable?
         let val = expr_to_val(*expr, ctx);
         let source_type = ctx.ast.expressions[*expr].exp_type.as_ref().unwrap();
         if (matches!(source_type, ExpressionType::Float(_)) && matches!(target_type, ExpressionType::Int(_)))
            || (matches!(source_type, ExpressionType::Int(_)) && matches!(target_type, ExpressionType::Float(_)))
         {
            writeln!(ctx.buf, "cast {}", val).unwrap();
         } else {
            writeln!(ctx.buf, "copy {}", val).unwrap();
         }
      }
      Expression::BoundFcnLiteral(_, _) => todo!(),
      Expression::UnresolvedStructLiteral(_, _) => unreachable!(),
      Expression::StructLiteral(_, _) => unreachable!(),
      Expression::EnumLiteral(_, _) => unreachable!(),
      Expression::UnresolvedEnumLiteral(_, _) => unreachable!(),
      Expression::UnresolvedProcLiteral(_, _) => unreachable!(),
      Expression::ArrayLiteral(_) => unreachable!(),
      Expression::IfX(_, _, _) => unreachable!(),
   }
}

fn write_call_expr(proc_expr: ExpressionId, args: &[ArgumentNode], ctx: &mut GenerationContext) {
   let callee = match ctx.ast.expressions[proc_expr].exp_type.as_ref().unwrap() {
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
            roland_type_to_abi_type(
               ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap(),
               ctx.udt,
               ctx.interner
            ),
            val
         )
         .unwrap();
      } else {
         write!(
            ctx.buf,
            "{} {}, ",
            roland_type_to_abi_type(
               ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap(),
               ctx.udt,
               ctx.interner
            ),
            val
         )
         .unwrap();
      }
   }
   writeln!(ctx.buf, ")").unwrap();
}
