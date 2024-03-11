use std::collections::HashSet;
use std::io::Write;

use indexmap::{IndexMap, IndexSet};
use slotmap::SecondaryMap;

use super::linearize::{Cfg, CfgInstruction, CFG_END_NODE, CFG_START_NODE};
use super::regalloc;
use super::wasm::type_as_zero_bytes;
use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::{Interner, StrId};
use crate::parse::{
   ArgumentNode, AstPool, CastType, Expression, ExpressionId, ProcImplSource, ProcedureId, UnOp, UserDefinedTypeId,
   UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::{GlobalInfo, ProcedureInfo};
use crate::size_info::{mem_alignment, sizeof_type_mem};
use crate::type_data::{
   ExpressionType, FloatWidth, IntType, IntWidth, F32_TYPE, F64_TYPE, I16_TYPE, I32_TYPE, I64_TYPE, I8_TYPE, U16_TYPE,
   U32_TYPE, U64_TYPE, U8_TYPE,
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
   global_info: &'a IndexMap<VariableId, GlobalInfo>,
}

fn roland_type_to_base_type(r_type: &ExpressionType) -> &'static str {
   match r_type {
      ExpressionType::Bool => "w",
      &F32_TYPE => "s",
      &F64_TYPE => "d",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Eight,
      })
      | ExpressionType::ProcedurePointer { .. } => "l",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Four | IntWidth::Two | IntWidth::One,
      }) => "w",
      _ => todo!(),
   }
}

fn roland_type_to_extended_type(r_type: &ExpressionType) -> &'static str {
   match r_type {
      ExpressionType::Bool => "b",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Two,
      }) => "h",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::One,
      }) => "b",
      _ => roland_type_to_base_type(r_type)
   }
}

fn roland_type_to_abi_type(r_type: &ExpressionType, udt: &UserDefinedTypeInfo, interner: &Interner) -> String {
   match r_type {
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
      }) | ExpressionType::Bool => "ub".into(),
      ExpressionType::Unit | ExpressionType::Never => "".into(), // TODO
      ExpressionType::Struct(sid) => {
         format!(":{}", interner.lookup(udt.struct_info.get(*sid).unwrap().name))
      }
      ExpressionType::Union(uid) => {
         format!(":{}", interner.lookup(udt.union_info.get(*uid).unwrap().name))
      }
      _ => roland_type_to_base_type(r_type).into()
   }
}

// TODO: we'll make this not alloc
fn roland_type_to_sub_type(r_type: &ExpressionType, udt: &UserDefinedTypeInfo, interner: &Interner) -> String {
   match r_type {
      ExpressionType::Struct(sid) => {
         format!(":{}", interner.lookup(udt.struct_info.get(*sid).unwrap().name))
      }
      ExpressionType::Union(uid) => {
         format!(":{}", interner.lookup(udt.union_info.get(*uid).unwrap().name))
      }
      _ => roland_type_to_extended_type(r_type).into()
   }
}

fn literal_as_bytes(buf: &mut Vec<u8>, expr_index: ExpressionId, generation_context: &GenerationContext) {
   let expr_node = &generation_context.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::BoundFcnLiteral(proc_id, _) => todo!(),
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(x) => {
         buf.extend(u8::from(*x).to_le_bytes());
      }
      Expression::EnumLiteral(_, _) => unreachable!(),
      Expression::IntLiteral { val: x, .. } => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => x.width,
            _ => unreachable!(),
         };
         match width {
            IntWidth::Eight => {
               buf.extend(x.to_le_bytes());
            }
            IntWidth::Four => {
               buf.extend((*x as u32).to_le_bytes());
            }
            IntWidth::Two => {
               buf.extend((*x as u16).to_le_bytes());
            }
            IntWidth::One => {
               buf.extend((*x as u8).to_le_bytes());
            }
            IntWidth::Pointer => unreachable!(),
         };
      }
      Expression::FloatLiteral(x) => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Float(x) => x.width,
            _ => unreachable!(),
         };
         match width {
            FloatWidth::Eight => {
               buf.extend(x.to_bits().to_le_bytes());
            }
            FloatWidth::Four => {
               buf.extend((*x as f32).to_bits().to_le_bytes());
            }
         }
      }
      Expression::StringLiteral(str) => todo!(),
      Expression::StructLiteral(s_id, fields) => {
         let si = generation_context.udt.struct_info.get(*s_id).unwrap();
         let ssi = generation_context
            .udt
            .struct_info
            .get(*s_id)
            .unwrap()
            .size
            .as_ref()
            .unwrap();
         for (field, next_field) in si.field_types.iter().zip(si.field_types.keys().skip(1)) {
            let value_of_field = fields.get(field.0).copied().unwrap();
            if let Some(val) = value_of_field {
               literal_as_bytes(buf, val, generation_context);
            } else {
               type_as_zero_bytes(buf, &field.1.e_type, generation_context.udt, Target::Qbe);
            }
            let this_offset = ssi.field_offsets_mem.get(field.0).unwrap();
            let next_offset = ssi.field_offsets_mem.get(next_field).unwrap();
            let padding_bytes =
               next_offset - this_offset - sizeof_type_mem(&field.1.e_type, generation_context.udt, Target::Qbe);
            for _ in 0..padding_bytes {
               buf.push(0);
            }
         }
         if let Some(last_field) = si.field_types.iter().last() {
            let value_of_field = fields.get(last_field.0).copied().unwrap();
            if let Some(val) = value_of_field {
               literal_as_bytes(buf, val, generation_context);
            } else {
               type_as_zero_bytes(buf, &last_field.1.e_type, generation_context.udt, Target::Qbe);
            }
            let this_offset = ssi.field_offsets_mem.get(last_field.0).unwrap();
            let next_offset = ssi.mem_size;
            let padding_bytes =
               next_offset - this_offset - sizeof_type_mem(&last_field.1.e_type, generation_context.udt, Target::Qbe);
            for _ in 0..padding_bytes {
               buf.push(0);
            }
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            literal_as_bytes(buf, *expr, generation_context);
         }
      }
      _ => unreachable!(),
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
      global_info: &program.global_info,
   };

   for (i, string_literal) in ctx.string_literals.iter().enumerate() {
      let str = ctx.interner.lookup(*string_literal);
      write!(ctx.buf, "data $s{} = {{ b ", i).unwrap();
      for by in str.as_bytes() {
         write!(ctx.buf, "{} ", by).unwrap();
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   let mut global_bytes = vec![];
   for a_global in program.global_info.iter() {
      // TODO: skip zero size globals? ... add a test?
      write!(ctx.buf, "data $v{} = {{ ", a_global.0 .0).unwrap();
      match a_global.1.initializer {
         Some(e) => {
            literal_as_bytes(&mut global_bytes, e, &ctx);
            write!(ctx.buf, "b ").unwrap();
            for by in global_bytes.drain(..) {
               write!(ctx.buf, "{} ", by).unwrap();
            }
         }
         None => {
            // Just zero init
            write!(
               ctx.buf,
               "z {} ",
               sizeof_type_mem(&a_global.1.expr_type.e_type, ctx.udt, Target::Qbe)
            )
            .unwrap();
         }
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   fn emit_aggregate(
      buf: &mut Vec<u8>,
      emitted: &mut HashSet<UserDefinedTypeId>,
      udt: &UserDefinedTypeInfo,
      interner: &Interner,
      id: UserDefinedTypeId,
   ) {
      // All this complication is because we must emit the definition of an aggregate before it is used
      if !emitted.insert(id) {
         return;
      }

      match id {
         UserDefinedTypeId::Struct(sid) => {
            let si = udt.struct_info.get(sid).unwrap();
            for field_t in si.field_types.iter().map(|x| &x.1.e_type) {
               match field_t {
                  ExpressionType::Struct(f_sid) => {
                     emit_aggregate(buf, emitted, udt, interner, UserDefinedTypeId::Struct(*f_sid));
                  }
                  ExpressionType::Union(f_uid) => {
                     emit_aggregate(buf, emitted, udt, interner, UserDefinedTypeId::Union(*f_uid));
                  }
                  _ => (),
               }
            }

            write!(buf, "type :{} = {{ ", interner.lookup(si.name)).unwrap();
            for (i, field_type) in si.field_types.values().map(|x| &x.e_type).enumerate() {
               if i == si.field_types.len() - 1 {
                  write!(buf, "{}", roland_type_to_sub_type(field_type, udt, interner)).unwrap();
               } else {
                  write!(buf, "{}, ", roland_type_to_sub_type(field_type, udt, interner)).unwrap();
               }
            }
         }
         UserDefinedTypeId::Union(uid) => {
            let ui = udt.union_info.get(uid).unwrap();
            for field_t in ui.field_types.iter().map(|x| &x.1.e_type) {
               match field_t {
                  ExpressionType::Struct(f_sid) => {
                     emit_aggregate(buf, emitted, udt, interner, UserDefinedTypeId::Struct(*f_sid));
                  }
                  ExpressionType::Union(f_uid) => {
                     emit_aggregate(buf, emitted, udt, interner, UserDefinedTypeId::Union(*f_uid));
                  }
                  _ => (),
               }
            }

            write!(buf, "type :{} = {{ ", interner.lookup(ui.name)).unwrap();
            for (i, field_type) in ui.field_types.values().map(|x| &x.e_type).enumerate() {
               if i == ui.field_types.len() - 1 {
                  write!(buf, "{{ {} }}", roland_type_to_sub_type(field_type, udt, interner)).unwrap();
               } else {
                  write!(buf, "{{ {} }} ", roland_type_to_sub_type(field_type, udt, interner)).unwrap();
               }
            }
         }
         UserDefinedTypeId::Enum(_) => unreachable!(),
      }
      writeln!(buf, " }}").unwrap();
   }

   let mut emitted_aggregates = HashSet::new();

   for a_struct in program.user_defined_types.struct_info.keys() {
      emit_aggregate(
         &mut ctx.buf,
         &mut emitted_aggregates,
         ctx.udt,
         ctx.interner,
         UserDefinedTypeId::Struct(a_struct),
      );
   }

   for a_union in program.user_defined_types.union_info.keys() {
      emit_aggregate(
         &mut ctx.buf,
         &mut emitted_aggregates,
         ctx.udt,
         ctx.interner,
         UserDefinedTypeId::Union(a_union),
      );
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

   for (_, procedure) in program
      .procedures
      .iter()
      .filter(|x| matches!(x.1.proc_impl, ProcImplSource::Builtin))
   {
      write!(
         ctx.buf,
         "function {} ${}(",
         roland_type_to_abi_type(&procedure.definition.ret_type.e_type, ctx.udt, ctx.interner),
         interner.lookup(procedure.definition.name.str)
      )
      .unwrap();
      for (i, param) in procedure.definition.parameters.iter().enumerate() {
         write!(
            ctx.buf,
            "{} %p{}",
            roland_type_to_abi_type(&param.p_type.e_type, ctx.udt, ctx.interner),
            param.var_id.0,
         )
         .unwrap();

         if i != procedure.definition.parameters.len() - 1 {
            write!(ctx.buf, ", ").unwrap();
         }
      }
      writeln!(ctx.buf, ") {{").unwrap();
      writeln!(ctx.buf, "@entry").unwrap();
      match interner.lookup(procedure.definition.name.str) {
         "unreachable" | _ => {
            writeln!(ctx.buf, "   hlt").unwrap();
         }
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
         } else if ctx.global_info.contains_key(&v) {
            Some(format!("$v{}", v.0))
         } else {
            Some(format!("%v{}", v.0))
         }
      }
      Expression::UnaryOperator(UnOp::Dereference, e) => Some(expr_to_val(e, ctx)),
      Expression::UnaryOperator(UnOp::AddressOf, e) => compute_offset(e, ctx),
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
            debug_assert!(!expression_could_have_side_effects(*en, &ctx.ast.expressions));
            if ctx.is_main {
               // World's biggest hack
               writeln!(&mut ctx.buf, "   ret 0").unwrap();
            } else {
               // this whole thing is pretty suspect?
               if *ctx.ast.expressions[*en].exp_type.as_ref().unwrap() == ExpressionType::Never {
                  writeln!(&mut ctx.buf, "   hlt").unwrap();
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
         } else if ctx.global_info.contains_key(v) {
            format!("$v{}", v.0)
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
            let lt = rhs_mem.unwrap();
            match ren.exp_type.as_ref().unwrap() {
               ExpressionType::Bool | &U8_TYPE => {
                  writeln!(ctx.buf, "loadub {}", lt).unwrap();
               }
               &I8_TYPE => {
                  writeln!(ctx.buf, "loadsb {}", lt).unwrap();
               }
               &U16_TYPE => {
                  writeln!(ctx.buf, "loaduh {}", lt).unwrap();
               }
               &I16_TYPE => {
                  writeln!(ctx.buf, "loadsh {}", lt).unwrap();
               }
               &U32_TYPE => {
                  writeln!(ctx.buf, "loaduw {}", lt).unwrap();
               }
               &I32_TYPE => {
                  writeln!(ctx.buf, "loadsw {}", lt).unwrap();
               }
               &U64_TYPE | &I64_TYPE => {
                  writeln!(ctx.buf, "loadl {}", lt).unwrap();
               }
               &F32_TYPE => {
                  writeln!(ctx.buf, "loads {}", lt).unwrap();
               }
               &F64_TYPE => {
                  writeln!(ctx.buf, "loads {}", lt).unwrap();
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
            crate::parse::BinOp::Divide => match typ {
               &F32_TYPE | &F64_TYPE => "div",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: _,
               }) => "udiv",
               ExpressionType::Int(IntType { signed: true, width: _ }) => "div",
               _ => unreachable!(),
            },
            crate::parse::BinOp::Remainder => match typ {
               ExpressionType::Int(IntType {
                  signed: false,
                  width: _,
               }) => "urem",
               ExpressionType::Int(IntType { signed: true, width: _ }) => "rem",
               _ => unreachable!(),
            },
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
            crate::parse::BinOp::NotEquality => match typ {
               ExpressionType::Bool => "cnew",
               &F32_TYPE => "cnes",
               &F64_TYPE => "cned",
               ExpressionType::Int(IntType {
                  signed: _,
                  width: IntWidth::Eight,
               }) => "cnel",
               ExpressionType::Int(IntType {
                  signed: _,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "cnew",
               _ => unreachable!(),
            },
            crate::parse::BinOp::GreaterThan => match typ {
               ExpressionType::Bool => "cugtw",
               &F32_TYPE => "cgts",
               &F64_TYPE => "cgtd",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Eight,
               }) => "cugtl",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "cugtw",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Eight,
               }) => "csgtl",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "csgtw",
               _ => unreachable!(),
            },
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
            crate::parse::BinOp::LessThanOrEqualTo => match typ {
               ExpressionType::Bool => "culew",
               &F32_TYPE => "cles",
               &F64_TYPE => "cled",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Eight,
               }) => "culel",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "culew",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Eight,
               }) => "cslel",
               ExpressionType::Int(IntType {
                  signed: true,
                  width: IntWidth::Four | IntWidth::Two | IntWidth::One,
               }) => "cslew",
               _ => unreachable!(),
            },
            crate::parse::BinOp::BitwiseAnd => "and",
            crate::parse::BinOp::BitwiseOr => "or",
            crate::parse::BinOp::BitwiseXor => "xor",
            crate::parse::BinOp::BitwiseLeftShift => "shl",
            crate::parse::BinOp::BitwiseRightShift => match typ {
               ExpressionType::Int(IntType { signed: true, width: _ }) => "sar",
               ExpressionType::Int(IntType {
                  signed: false,
                  width: _,
               }) => "shr",
               _ => unreachable!(),
            },
            crate::parse::BinOp::LogicalAnd => unreachable!(),
            crate::parse::BinOp::LogicalOr => unreachable!(),
         };
         let lhs_val = expr_to_val(*lhs, ctx);
         let rhs_val = expr_to_val(*rhs, ctx);
         writeln!(ctx.buf, "{} {}, {}", opcode, lhs_val, rhs_val).unwrap();
      }
      Expression::UnaryOperator(UnOp::AddressOf, inner_id) => {
         let e = &ctx.ast.expressions[*inner_id];
         if let ExpressionType::ProcedureItem(proc_id, _bound_type_params) = e.exp_type.as_ref().unwrap() {
            // TODO: need to do name mangling here, as with call
            let proc_name = ctx.interner.lookup(ctx.proc_info[*proc_id].name.str);
            writeln!(ctx.buf, "copy ${}", proc_name).unwrap();
         } else {
            writeln!(ctx.buf, "copy {}", rhs_mem.unwrap()).unwrap()
         }
      },
      Expression::UnaryOperator(operator, inner_id) => {
         let inner_val = expr_to_val(*inner_id, ctx);
         match operator {
            crate::parse::UnOp::Negate => writeln!(ctx.buf, "neg {}", inner_val).unwrap(),
            crate::parse::UnOp::Complement => {
               if *ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap() == ExpressionType::Bool {
                  writeln!(ctx.buf, "ceqw {}, 0", inner_val).unwrap()
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
            crate::parse::UnOp::AddressOf => unreachable!(),
            crate::parse::UnOp::Dereference => match ren.exp_type.as_ref().unwrap() {
               ExpressionType::Bool | &U8_TYPE => {
                  writeln!(ctx.buf, "loadub {}", inner_val).unwrap();
               }
               &I8_TYPE => {
                  writeln!(ctx.buf, "loadsb {}", inner_val).unwrap();
               }
               &U16_TYPE => {
                  writeln!(ctx.buf, "loaduh {}", inner_val).unwrap();
               }
               &I16_TYPE => {
                  writeln!(ctx.buf, "loadsh {}", inner_val).unwrap();
               }
               &U32_TYPE => {
                  writeln!(ctx.buf, "loaduw {}", inner_val).unwrap();
               }
               &I32_TYPE => {
                  writeln!(ctx.buf, "loadsw {}", inner_val).unwrap();
               }
               &U64_TYPE | &I64_TYPE => {
                  writeln!(ctx.buf, "loadl {}", inner_val).unwrap();
               }
               &F32_TYPE => {
                  writeln!(ctx.buf, "loads {}", inner_val).unwrap();
               }
               &F64_TYPE => {
                  writeln!(ctx.buf, "loads {}", inner_val).unwrap();
               }
               _ => unreachable!(),
            },
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
         let src_type = ctx.ast.expressions[*expr].exp_type.as_ref().unwrap();
         let val = expr_to_val(*expr, ctx);
         match (src_type, target_type) {
            (ExpressionType::Int(l), ExpressionType::Int(r))
               if l.width.as_num_bytes(Target::Qbe) >= r.width.as_num_bytes(Target::Qbe) =>
            {
               writeln!(ctx.buf, "copy {}", val).unwrap();
            }
            (ExpressionType::Int(l), ExpressionType::Int(r))
               if l.width.as_num_bytes(Target::Qbe) < r.width.as_num_bytes(Target::Qbe) =>
            {
               if l.width.as_num_bytes(Target::Qbe) <= 4 && r.width == IntWidth::Eight {
                  if l.signed {
                     writeln!(ctx.buf, "extsw {}", val).unwrap();
                  } else {
                     writeln!(ctx.buf, "extuw {}", val).unwrap();
                  }
               } else if l.width == IntWidth::One && r.width == IntWidth::Two && l.signed && !r.signed {
                  writeln!(ctx.buf, "and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111).unwrap();
               } else {
                  writeln!(ctx.buf, "copy {}", val).unwrap();
               }
            }
            (&F64_TYPE, &F32_TYPE) => {
               writeln!(ctx.buf, "truncd {}", val).unwrap();
            }
            (&F32_TYPE, &F64_TYPE) => {
               writeln!(ctx.buf, "exts {}", val).unwrap();
            }
            (ExpressionType::Float(_), ExpressionType::Int(_)) => {
               todo!()
            }
            (ExpressionType::Int(_), ExpressionType::Float(_)) => {
               todo!()
            }
            (ExpressionType::Bool, ExpressionType::Int(i)) => {
               if i.width == IntWidth::Eight {
                  writeln!(ctx.buf, "extuw {}", val).unwrap();
               } else {
                  writeln!(ctx.buf, "copy {}", val).unwrap();
               }
            }
            _ => writeln!(ctx.buf, "copy {}", val).unwrap(),
         }
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
   match ctx.ast.expressions[proc_expr].exp_type.as_ref().unwrap() {
      ExpressionType::ProcedureItem(id, _) => {
         let callee = ctx.interner.lookup(ctx.proc_info[*id].name.str);
         write!(ctx.buf, "call ${}(", callee).unwrap();
      }
      ExpressionType::ProcedurePointer { .. } => {
         let val = expr_to_val(proc_expr, ctx);
         write!(ctx.buf, "call {}(", val).unwrap();
      }
      _ => unreachable!(),
   };
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
