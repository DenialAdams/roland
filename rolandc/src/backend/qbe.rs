use std::borrow::Cow;
use std::collections::HashMap;
use std::io::Write;

use indexmap::{IndexMap, IndexSet};
use slotmap::{Key, SlotMap};

use super::linearize::{CFG_END_NODE, Cfg, CfgInstruction};
use super::regalloc::{RegallocResult, VarSlot};
use crate::backend::linearize::post_order;
use crate::backend::regalloc::RegisterType;
use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::{Interner, StrId};
use crate::parse::{
   ArgumentNode, AstPool, BinOp, CastType, Expression, ExpressionId, ProcImplSource, ProcedureId, ProcedureNode, UnOp,
   UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::GlobalInfo;
use crate::size_info::sizeof_type_mem;
use crate::type_data::{
   ExpressionType, F32_TYPE, F64_TYPE, FloatType, FloatWidth, I8_TYPE, I16_TYPE, I32_TYPE, I64_TYPE, IntType, IntWidth,
   U8_TYPE, U16_TYPE, U32_TYPE, U64_TYPE,
};
use crate::{BaseTarget, Program};

struct GenerationContext<'a> {
   buf: Vec<u8>,
   var_to_slot: IndexMap<VariableId, VarSlot>,
   ast: &'a AstPool,
   procedures: &'a SlotMap<ProcedureId, ProcedureNode>,
   interner: &'a Interner,
   udt: &'a UserDefinedTypeInfo,
   string_literals: &'a IndexSet<StrId>,
   global_info: &'a IndexMap<VariableId, GlobalInfo>,
   aggregate_defs: IndexSet<ExpressionType>,
}

fn roland_type_to_base_type(r_type: &ExpressionType) -> &'static str {
   match r_type {
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
      })
      | ExpressionType::Bool => "w",
      _ => unreachable!(),
   }
}

fn roland_type_to_extended_type(r_type: &ExpressionType) -> &'static str {
   match r_type {
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::Two,
      }) => "h",
      ExpressionType::Int(IntType {
         signed: _,
         width: IntWidth::One,
      })
      | ExpressionType::Bool => "b",
      _ => roland_type_to_base_type(r_type),
   }
}

fn roland_type_to_abi_type(
   r_type: &ExpressionType,
   udt: &UserDefinedTypeInfo,
   aggregate_defs: &IndexSet<ExpressionType>,
) -> Option<Cow<'static, str>> {
   if sizeof_type_mem(r_type, udt, BaseTarget::Qbe) == 0 {
      return None;
   }
   Some(match r_type {
      ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::Two,
      }) => Cow::Borrowed("sh"),
      ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::Two,
      }) => Cow::Borrowed("uh"),
      ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::One,
      }) => Cow::Borrowed("sb"),
      ExpressionType::Int(IntType {
         signed: false,
         width: IntWidth::One,
      })
      | ExpressionType::Bool => Cow::Borrowed("ub"),
      ExpressionType::Struct(_, _) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":s{}", index))
      }
      ExpressionType::Union(_, _) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":u{}", index))
      }
      ExpressionType::Array(_, _) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":a{}", index))
      }
      _ => Cow::Borrowed(roland_type_to_base_type(r_type)),
   })
}

fn roland_type_to_sub_type(
   r_type: &ExpressionType,
   udt: &UserDefinedTypeInfo,
   aggregate_defs: &IndexSet<ExpressionType>,
) -> Option<Cow<'static, str>> {
   if sizeof_type_mem(r_type, udt, BaseTarget::Qbe) == 0 {
      return None;
   }
   Some(match r_type {
      ExpressionType::Struct(_, _) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":s{}", index))
      }
      ExpressionType::Union(_, _) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":u{}", index))
      }
      ExpressionType::Array(_, _) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":a{}", index))
      }
      _ => Cow::Borrowed(roland_type_to_extended_type(r_type)),
   })
}

fn literal_as_data(expr_index: ExpressionId, ctx: &mut GenerationContext) {
   let expr_node = &ctx.ast.expressions[expr_index];
   match &expr_node.expression {
      Expression::BoundFcnLiteral(proc_id, _) => {
         write!(
            ctx.buf,
            "l ${}, ",
            mangle(*proc_id, &ctx.procedures[*proc_id], ctx.interner)
         )
         .unwrap();
      }
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(x) => {
         write!(ctx.buf, "b {}, ", u8::from(*x)).unwrap();
      }
      Expression::IntLiteral { val: x, .. } => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Int(x) => x.width,
            _ => unreachable!(),
         };
         match width {
            IntWidth::Eight => {
               write!(ctx.buf, "l {}, ", *x).unwrap();
            }
            IntWidth::Four => {
               write!(ctx.buf, "w {}, ", *x).unwrap();
            }
            IntWidth::Two => {
               write!(ctx.buf, "h {}, ", *x).unwrap();
            }
            IntWidth::One => {
               write!(ctx.buf, "b {}, ", *x).unwrap();
            }
            IntWidth::Pointer => unreachable!(),
         }
      }
      Expression::FloatLiteral(x) => {
         let width = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Float(x) => x.width,
            _ => unreachable!(),
         };
         match width {
            FloatWidth::Eight => {
               write!(ctx.buf, "d {}, ", x.to_bits()).unwrap();
            }
            FloatWidth::Four => {
               write!(ctx.buf, "s {}, ", (*x as f32).to_bits()).unwrap();
            }
         }
      }
      Expression::StringLiteral(str) => {
         let (string_index, string_id) = ctx.string_literals.get_full(str).unwrap();
         let length = ctx.interner.lookup(*string_id).len();
         write!(ctx.buf, "l $.s{}, l {}, ", string_index, length).unwrap();
      }
      Expression::StructLiteral(s_id, fields) => {
         let si = ctx.udt.struct_info.get(*s_id).unwrap();
         let ssi = ctx.udt.struct_info.get(*s_id).unwrap().size.as_ref().unwrap();
         for (field, next_offset) in si.field_types.iter().zip(
            si.field_types
               .keys()
               .skip(1)
               .map(|x| ssi.field_offsets_mem[x])
               .chain(std::iter::once(ssi.mem_size)),
         ) {
            let value_of_field = fields.get(field.0).copied().unwrap();
            if let Some(val) = value_of_field {
               literal_as_data(val, ctx);
            } else {
               let sz = sizeof_type_mem(&field.1.e_type, ctx.udt, BaseTarget::Qbe);
               if sz > 0 {
                  write!(ctx.buf, "z {}, ", sz).unwrap();
               }
            }
            let this_offset = ssi.field_offsets_mem.get(field.0).unwrap();
            let padding_bytes = next_offset - this_offset - sizeof_type_mem(&field.1.e_type, ctx.udt, BaseTarget::Qbe);
            if padding_bytes > 0 {
               write!(ctx.buf, "z {}, ", padding_bytes).unwrap();
            }
         }
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            literal_as_data(*expr, ctx);
         }
      }
      _ => unreachable!(),
   }
}

pub fn emit_qbe(program: &mut Program, interner: &Interner, regalloc_result: RegallocResult) -> Vec<u8> {
   fn emit_aggregate_def(
      buf: &mut Vec<u8>,
      emitted: &mut IndexSet<ExpressionType>,
      udt: &UserDefinedTypeInfo,
      et: &ExpressionType,
   ) {
      if !et.is_aggregate() {
         return;
      }

      if emitted.contains(et) {
         return;
      }

      if sizeof_type_mem(et, udt, BaseTarget::Qbe) == 0 {
         return;
      }

      let index = emitted.insert_full(et.clone()).0;

      match et {
         ExpressionType::Struct(sid, _) => {
            let si = udt.struct_info.get(*sid).unwrap();
            let ssi = si.size.as_ref().unwrap();
            for field_t in si.field_types.iter().map(|x| &x.1.e_type) {
               emit_aggregate_def(buf, emitted, udt, field_t);
            }

            write!(buf, "type :s{} = {{ ", index).unwrap();
            for (field, next_offset) in si.field_types.iter().zip(
               si.field_types
                  .keys()
                  .skip(1)
                  .map(|x| ssi.field_offsets_mem[x])
                  .chain(std::iter::once(ssi.mem_size)),
            ) {
               if let Some(ft) = roland_type_to_sub_type(&field.1.e_type, udt, emitted) {
                  write!(buf, "{}, ", ft).unwrap();
               }
               let this_offset = ssi.field_offsets_mem.get(field.0).unwrap();
               let padding_bytes = next_offset - this_offset - sizeof_type_mem(&field.1.e_type, udt, BaseTarget::Qbe);
               if padding_bytes > 0 {
                  write!(buf, "b {}, ", padding_bytes).unwrap();
               }
            }
            writeln!(buf, "}}").unwrap();
         }
         ExpressionType::Union(uid, _) => {
            let ui = udt.union_info.get(*uid).unwrap();
            for field_t in ui.field_types.iter().map(|x| &x.1.e_type) {
               emit_aggregate_def(buf, emitted, udt, field_t);
            }
            write!(buf, "type :u{} = {{ ", index).unwrap();
            for field_type in ui.field_types.values().map(|x| &x.e_type) {
               if let Some(ft_as_qbe) = roland_type_to_sub_type(field_type, udt, emitted) {
                  write!(buf, "{{ {} }} ", ft_as_qbe).unwrap();
               }
            }
            writeln!(buf, " }}").unwrap();
         }
         ExpressionType::Array(base_ty, len) => {
            emit_aggregate_def(buf, emitted, udt, base_ty);
            let basety_as_qbe = roland_type_to_sub_type(base_ty, udt, emitted).unwrap();
            writeln!(buf, "type :a{} = {{ {} {} }}", index, basety_as_qbe, len).unwrap();
         }
         _ => unreachable!(),
      }
   }

   let mut ctx = GenerationContext {
      buf: vec![],
      var_to_slot: regalloc_result.var_to_slot,
      ast: &program.ast,
      procedures: &program.procedures,
      interner,
      udt: &program.user_defined_types,
      string_literals: &program.literals,
      global_info: &program.non_stack_var_info,
      aggregate_defs: IndexSet::new(),
   };

   for (i, string_literal) in ctx.string_literals.iter().enumerate() {
      let str = ctx.interner.lookup(*string_literal);
      // We prefix with a dot to avoid any conflict with user-named exported functions
      write!(ctx.buf, "data $.s{} = {{ b ", i).unwrap();
      for by in str.as_bytes() {
         write!(ctx.buf, "{} ", by).unwrap();
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   for a_global in program.non_stack_var_info.iter() {
      write!(ctx.buf, "data $.v{} = {{ ", a_global.0.0).unwrap();
      match a_global.1.initializer {
         Some(e) => {
            literal_as_data(e, &mut ctx);
         }
         None => {
            // Just zero init
            write!(
               ctx.buf,
               "z {} ",
               sizeof_type_mem(&a_global.1.expr_type.e_type, ctx.udt, BaseTarget::Qbe)
            )
            .unwrap();
         }
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   for procedure in program.procedures.values() {
      for param_type in procedure.definition.parameters.iter().map(|x| &x.p_type.e_type) {
         emit_aggregate_def(&mut ctx.buf, &mut ctx.aggregate_defs, ctx.udt, param_type);
      }
      emit_aggregate_def(
         &mut ctx.buf,
         &mut ctx.aggregate_defs,
         ctx.udt,
         &procedure.definition.ret_type.e_type,
      );
   }

   for (proc_id, procedure) in program.procedures.iter() {
      let Some(cfg) = program.procedure_bodies.get(proc_id).map(|x| &x.cfg) else {
         continue;
      };

      let abi_ret_type = roland_type_to_abi_type(&procedure.definition.ret_type.e_type, ctx.udt, &ctx.aggregate_defs)
         .unwrap_or_else(|| "".into());
      write!(
         ctx.buf,
         "function {} ${}(",
         abi_ret_type,
         mangle(proc_id, &ctx.procedures[proc_id], ctx.interner)
      )
      .unwrap();
      let mut stack_params = HashMap::new();
      let mut p_i = 0;
      for param in procedure.definition.parameters.iter() {
         if let Some(p_type) = roland_type_to_abi_type(&param.p_type.e_type, ctx.udt, &ctx.aggregate_defs) {
            match ctx.var_to_slot.get(&param.var_id).copied() {
               Some(VarSlot::Register(reg)) => {
                  write!(ctx.buf, "{} %r{}, ", p_type, reg).unwrap();
               }
               Some(VarSlot::Stack(v)) => {
                  if param.p_type.e_type.is_aggregate() {
                     write!(ctx.buf, "{} %v{}, ", p_type, v).unwrap();
                  } else {
                     write!(ctx.buf, "{} %r{}, ", p_type, p_i).unwrap();
                  }
                  stack_params.insert(v as usize, (&param.p_type.e_type, p_i));
               }
               None => {
                  // This parameter was not assigned a slot - this variable MUST be unused
                  // we'll just give it some value
                  write!(ctx.buf, "{} %p{}, ", p_type, p_i).unwrap();
               }
            }
            p_i += 1;
         }
      }
      writeln!(ctx.buf, ") {{").unwrap();
      // Allocate stack
      writeln!(ctx.buf, "@entry").unwrap();
      for (i, (sz, alignment)) in regalloc_result.procedure_stack_slots[proc_id]
         .iter()
         .copied()
         .enumerate()
      {
         let reg_and_suffix = match stack_params.get(&i) {
            Some((e_type, _)) if e_type.is_aggregate() => {
               continue;
            }
            Some((e_type, param_index)) => Some((param_index, roland_type_to_extended_type(e_type))),
            None => None,
         };
         writeln!(ctx.buf, "   %v{} =l alloc{} {}", i, alignment, sz,).unwrap();
         if let Some((reg_idx, suffix)) = reg_and_suffix {
            writeln!(ctx.buf, "   store{} %r{}, %v{}", suffix, reg_idx, i).unwrap();
         }
      }
      for (i, typ) in regalloc_result.procedure_registers[proc_id].iter().enumerate() {
         let i = i + procedure.definition.parameters.len();
         match typ {
            RegisterType::I32 => writeln!(ctx.buf, "   %r{} =w copy 0", i).unwrap(),
            RegisterType::I64 => writeln!(ctx.buf, "   %r{} =l copy 0", i).unwrap(),
            RegisterType::F32 => writeln!(ctx.buf, "   %r{} =s copy 0", i).unwrap(),
            RegisterType::F64 => writeln!(ctx.buf, "   %r{} =d copy 0", i).unwrap(),
         }
      }
      for bb_id in post_order(cfg).iter().rev().copied().filter(|x| *x != CFG_END_NODE) {
         emit_bb(cfg, bb_id, &mut ctx);
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   for (proc_id, procedure) in program
      .procedures
      .iter()
      .filter(|x| x.1.impl_source == ProcImplSource::Builtin)
   {
      if interner.lookup(procedure.definition.name.str) != "unreachable" {
         // TODO: we should get better about pruning these dead builtins
         continue;
      }

      write!(
         ctx.buf,
         "function {} ${}(",
         roland_type_to_abi_type(&procedure.definition.ret_type.e_type, ctx.udt, &ctx.aggregate_defs)
            .unwrap_or_else(|| "".into()),
         mangle(proc_id, &ctx.procedures[proc_id], ctx.interner)
      )
      .unwrap();
      for (p_i, param) in procedure.definition.parameters.iter().enumerate() {
         if let Some(param_type) = roland_type_to_abi_type(&param.p_type.e_type, ctx.udt, &ctx.aggregate_defs) {
            write!(ctx.buf, "{} %p{}, ", param_type, p_i).unwrap();
         }
      }
      writeln!(ctx.buf, ") {{").unwrap();
      writeln!(ctx.buf, "@entry").unwrap();
      match interner.lookup(procedure.definition.name.str) {
         "unreachable" => {
            writeln!(ctx.buf, "   hlt").unwrap();
         }
         _ => unreachable!(),
      }
      writeln!(ctx.buf, "}}").unwrap();
   }

   ctx.buf
      .write_all(
         b"export
function $_start() {
@entry
   call $main()
   call $syscall1(l 231, l 0)
   hlt
}",
      )
      .unwrap();

   ctx.buf
}

fn compute_offset(expr: ExpressionId, ctx: &mut GenerationContext, is_lhs: bool) -> Option<String> {
   match ctx.ast.expressions[expr].expression {
      Expression::Variable(v) if is_lhs => {
         if ctx.global_info.contains_key(&v) {
            Some(format!("$.v{}", v.0))
         } else {
            match ctx.var_to_slot.get(&v).unwrap() {
               VarSlot::Register(_) => None,
               VarSlot::Stack(v) => Some(format!("%v{}", v)),
            }
         }
      }
      Expression::UnaryOperator(UnOp::Dereference, e) if is_lhs => Some(expr_to_val(e, ctx)),
      Expression::UnaryOperator(UnOp::Dereference, e) => compute_offset(e, ctx, true),
      _ => None,
   }
}

fn emit_bb(cfg: &Cfg, bb: usize, ctx: &mut GenerationContext) {
   writeln!(ctx.buf, "@b{}", bb).unwrap();
   for instr in cfg.bbs[bb].instructions.iter() {
      match instr {
         CfgInstruction::Nop => (),
         CfgInstruction::Assignment(lid, en) => {
            if let Some(lhs_mem) = compute_offset(*lid, ctx, true) {
               if let Some(rhs_mem) = compute_offset(*en, ctx, false) {
                  let size = sizeof_type_mem(
                     ctx.ast.expressions[*en].exp_type.as_ref().unwrap(),
                     ctx.udt,
                     BaseTarget::Qbe,
                  );
                  writeln!(ctx.buf, "   blit {}, {}, {}", rhs_mem, lhs_mem, size).unwrap();
               } else if ctx.ast.expressions[*en].exp_type.as_ref().unwrap().is_aggregate() {
                  let Expression::ProcedureCall { proc_expr, args } = &ctx.ast.expressions[*en].expression else {
                     unreachable!()
                  };
                  writeln!(
                     ctx.buf,
                     "   %t ={} {}",
                     roland_type_to_abi_type(
                        ctx.ast.expressions[*en].exp_type.as_ref().unwrap(),
                        ctx.udt,
                        &ctx.aggregate_defs
                     )
                     .unwrap(),
                     make_call_expr(*proc_expr, args, ctx)
                  )
                  .unwrap();
                  let size = sizeof_type_mem(
                     ctx.ast.expressions[*en].exp_type.as_ref().unwrap(),
                     ctx.udt,
                     BaseTarget::Qbe,
                  );
                  writeln!(ctx.buf, "   blit %t, {}, {}", lhs_mem, size).unwrap();
               } else {
                  let suffix = roland_type_to_extended_type(ctx.ast.expressions[*en].exp_type.as_ref().unwrap());
                  let val = expr_to_val(*en, ctx);
                  writeln!(ctx.buf, "   store{} {}, {}", suffix, val, lhs_mem).unwrap();
               }
            } else {
               let Expression::Variable(v) = ctx.ast.expressions[*lid].expression else {
                  unreachable!()
               };
               let Some(VarSlot::Register(reg)) = ctx.var_to_slot.get(&v).copied() else {
                  unreachable!()
               };

               let rhs_expr_node = &ctx.ast.expressions[*en];
               let rhs_expr = {
                  match &rhs_expr_node.expression {
                     Expression::ProcedureCall { proc_expr, args } => make_call_expr(*proc_expr, args, ctx),
                     Expression::BoolLiteral(v) => {
                        format!("copy {}", u8::from(*v))
                     }
                     Expression::IntLiteral { val, .. } => {
                        let signed = matches!(
                           rhs_expr_node.exp_type.as_ref().unwrap(),
                           ExpressionType::Int(IntType { signed: true, .. })
                        );
                        if signed {
                           format!("copy {}", *val as i64)
                        } else {
                           format!("copy {}", *val)
                        }
                     }
                     Expression::FloatLiteral(val) => match *rhs_expr_node.exp_type.as_ref().unwrap() {
                        F64_TYPE => format!("copy d_{}", val),
                        F32_TYPE => format!("copy s_{}", val),
                        _ => unreachable!(),
                     },
                     Expression::BoundFcnLiteral(proc_id, _) => {
                        debug_assert!(matches!(
                           rhs_expr_node.exp_type,
                           Some(ExpressionType::ProcedurePointer { .. })
                        ));
                        format!("copy ${}", mangle(*proc_id, &ctx.procedures[*proc_id], ctx.interner))
                     }
                     Expression::Variable(v) => {
                        if ctx.global_info.contains_key(v) {
                           format!("copy $.v{}", v.0)
                        } else {
                           match ctx.var_to_slot.get(v).unwrap() {
                              VarSlot::Register(_) => unreachable!(),
                              VarSlot::Stack(v) => format!("copy %v{}", v),
                           }
                        }
                     }
                     Expression::BinaryOperator { operator, lhs, rhs } => {
                        let typ = ctx.ast.expressions[*lhs].exp_type.as_ref().unwrap();
                        let opcode = match operator {
                           BinOp::Add => "add",
                           BinOp::Subtract => "sub",
                           BinOp::Multiply => "mul",
                           BinOp::Divide => match typ {
                              &F32_TYPE | &F64_TYPE | ExpressionType::Int(IntType { signed: true, width: _ }) => "div",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: _,
                              }) => "udiv",
                              _ => unreachable!(),
                           },
                           BinOp::Remainder => match typ {
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: _,
                              }) => "urem",
                              ExpressionType::Int(IntType { signed: true, width: _ }) => "rem",
                              _ => unreachable!(),
                           },
                           BinOp::Equality => match typ {
                              &F32_TYPE => "ceqs",
                              &F64_TYPE => "ceqd",
                              ExpressionType::Int(IntType {
                                 signed: _,
                                 width: IntWidth::Eight,
                              }) => "ceql",
                              ExpressionType::Int(IntType {
                                 signed: _,
                                 width: IntWidth::Four | IntWidth::Two | IntWidth::One,
                              })
                              | ExpressionType::Bool => "ceqw",
                              _ => unreachable!(),
                           },
                           BinOp::NotEquality => match typ {
                              &F32_TYPE => "cnes",
                              &F64_TYPE => "cned",
                              ExpressionType::Int(IntType {
                                 signed: _,
                                 width: IntWidth::Eight,
                              }) => "cnel",
                              ExpressionType::Int(IntType {
                                 signed: _,
                                 width: IntWidth::Four | IntWidth::Two | IntWidth::One,
                              })
                              | ExpressionType::Bool => "cnew",
                              _ => unreachable!(),
                           },
                           BinOp::GreaterThan => match typ {
                              &F32_TYPE => "cgts",
                              &F64_TYPE => "cgtd",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Eight,
                              }) => "cugtl",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Four | IntWidth::Two | IntWidth::One,
                              })
                              | ExpressionType::Bool => "cugtw",
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
                           BinOp::LessThan => match typ {
                              &F32_TYPE => "clts",
                              &F64_TYPE => "cltd",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Eight,
                              }) => "cultl",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Four | IntWidth::Two | IntWidth::One,
                              })
                              | ExpressionType::Bool => "cultw",
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
                           BinOp::GreaterThanOrEqualTo => match typ {
                              &F32_TYPE => "cges",
                              &F64_TYPE => "cged",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Eight,
                              }) => "cugel",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Four | IntWidth::Two | IntWidth::One,
                              })
                              | ExpressionType::Bool => "cugew",
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
                           BinOp::LessThanOrEqualTo => match typ {
                              &F32_TYPE => "cles",
                              &F64_TYPE => "cled",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Eight,
                              }) => "culel",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: IntWidth::Four | IntWidth::Two | IntWidth::One,
                              })
                              | ExpressionType::Bool => "culew",
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
                           BinOp::BitwiseAnd => "and",
                           BinOp::BitwiseOr => "or",
                           BinOp::BitwiseXor => "xor",
                           BinOp::BitwiseLeftShift => "shl",
                           BinOp::BitwiseRightShift => match typ {
                              ExpressionType::Int(IntType { signed: true, width: _ }) => "sar",
                              ExpressionType::Int(IntType {
                                 signed: false,
                                 width: _,
                              }) => "shr",
                              _ => unreachable!(),
                           },
                           BinOp::LogicalAnd | BinOp::LogicalOr => unreachable!(),
                        };
                        let lhs_val = expr_to_val(*lhs, ctx);
                        let rhs_val = expr_to_val(*rhs, ctx);
                        format!("{} {}, {}", opcode, lhs_val, rhs_val)
                     }
                     Expression::UnaryOperator(UnOp::TakeProcedurePointer, inner_id) => {
                        let ExpressionType::ProcedureItem(proc_id, _bound_type_params) =
                           ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap()
                        else {
                           unreachable!();
                        };
                        format!("copy ${}", mangle(*proc_id, &ctx.procedures[*proc_id], ctx.interner))
                     }
                     Expression::UnaryOperator(operator, inner_id) => match operator {
                        UnOp::Negate => {
                           let inner_val = expr_to_val(*inner_id, ctx);
                           format!("neg {}", inner_val)
                        }
                        UnOp::Complement => {
                           let inner_val = expr_to_val(*inner_id, ctx);
                           if *ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap() == ExpressionType::Bool {
                              format!("ceqw {}, 0", inner_val)
                           } else {
                              let magic_const: u64 = match *ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap() {
                                 crate::type_data::U8_TYPE => u64::from(u8::MAX),
                                 crate::type_data::U16_TYPE => u64::from(u16::MAX),
                                 crate::type_data::U32_TYPE
                                 | crate::type_data::I8_TYPE
                                 | crate::type_data::I16_TYPE
                                 | crate::type_data::I32_TYPE => u64::from(u32::MAX),
                                 crate::type_data::I64_TYPE | crate::type_data::U64_TYPE => u64::MAX,
                                 _ => unreachable!(),
                              };
                              format!("xor {}, {}", inner_val, magic_const)
                           }
                        }
                        UnOp::Dereference => {
                           if let Expression::Variable(v) = ctx.ast.expressions[*inner_id].expression {
                              if let Some(VarSlot::Register(reg)) = ctx.var_to_slot.get(&v) {
                                 format!("copy %r{}", reg)
                              } else {
                                 let inner_val = expr_to_val(*inner_id, ctx);
                                 make_load(&inner_val, rhs_expr_node.exp_type.as_ref().unwrap())
                              }
                           } else {
                              let inner_val = expr_to_val(*inner_id, ctx);
                              make_load(&inner_val, rhs_expr_node.exp_type.as_ref().unwrap())
                           }
                        }
                        UnOp::AddressOf | UnOp::TakeProcedurePointer => unreachable!(),
                     },
                     Expression::Cast {
                        cast_type: CastType::As,
                        target_type,
                        expr,
                     } => {
                        let src_type = ctx.ast.expressions[*expr].exp_type.as_ref().unwrap();
                        let val = expr_to_val(*expr, ctx);
                        match (src_type, target_type) {
                           (ExpressionType::Int(l), ExpressionType::Int(r))
                              if l.width.as_num_bytes(BaseTarget::Qbe) >= r.width.as_num_bytes(BaseTarget::Qbe) =>
                           {
                              match (l.width, r.width) {
                                 (IntWidth::Eight | IntWidth::Four, IntWidth::Two) => {
                                    if r.signed {
                                       format!("extsh {}", val)
                                    } else {
                                       format!("and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111)
                                    }
                                 }
                                 (IntWidth::Eight | IntWidth::Four | IntWidth::Two, IntWidth::One) => {
                                    if r.signed {
                                       format!("extsb {}", val)
                                    } else {
                                       format!("and {}, {}", val, 0b0000_0000_0000_0000_0000_0000_1111_1111)
                                    }
                                 }
                                 (IntWidth::Two, IntWidth::Two) => {
                                    if !l.signed && r.signed {
                                       format!("extsh {}", val)
                                    } else if l.signed && !r.signed {
                                       format!("and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111)
                                    } else {
                                       format!("copy {}", val)
                                    }
                                 }
                                 (IntWidth::One, IntWidth::One) => {
                                    if !l.signed && r.signed {
                                       format!("extsb {}", val)
                                    } else if l.signed && !r.signed {
                                       format!("and {}, {}", val, 0b0000_0000_0000_0000_0000_0000_1111_1111)
                                    } else {
                                       format!("copy {}", val)
                                    }
                                 }
                                 _ => format!("copy {}", val),
                              }
                           }
                           (ExpressionType::Int(l), ExpressionType::Int(r))
                              if l.width.as_num_bytes(BaseTarget::Qbe) < r.width.as_num_bytes(BaseTarget::Qbe) =>
                           {
                              if l.width.as_num_bytes(BaseTarget::Qbe) <= 4 && r.width == IntWidth::Eight {
                                 if l.signed {
                                    format!("extsw {}", val)
                                 } else {
                                    format!("extuw {}", val)
                                 }
                              } else if l.width == IntWidth::One && r.width == IntWidth::Two && l.signed && !r.signed {
                                 format!("and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111)
                              } else {
                                 format!("copy {}", val)
                              }
                           }
                           (&F64_TYPE, &F32_TYPE) => {
                              format!("truncd {}", val)
                           }
                           (&F32_TYPE, &F64_TYPE) => {
                              format!("exts {}", val)
                           }
                           (
                              ExpressionType::Float(FloatType { width: src_width }),
                              ExpressionType::Int(IntType { signed, .. }),
                           ) => match src_width {
                              FloatWidth::Eight => {
                                 if *signed {
                                    format!("dtosi {}", val)
                                 } else {
                                    format!("dtoui {}", val)
                                 }
                              }
                              FloatWidth::Four => {
                                 if *signed {
                                    format!("stosi {}", val)
                                 } else {
                                    format!("stoui {}", val)
                                 }
                              }
                           },
                           (
                              ExpressionType::Int(IntType {
                                 signed,
                                 width: src_width,
                              }),
                              ExpressionType::Float(_),
                           ) => match (src_width, signed) {
                              (IntWidth::Eight, true) => format!("sltof {}", val),
                              (IntWidth::Eight, false) => format!("ultof {}", val),
                              (_, true) => format!("swtof {}", val),
                              (_, false) => format!("uwtof {}", val),
                           },
                           (ExpressionType::Bool, ExpressionType::Int(i)) => {
                              if i.width == IntWidth::Eight {
                                 format!("extuw {}", val)
                              } else {
                                 format!("copy {}", val)
                              }
                           }
                           _ => format!("copy {}", val),
                        }
                     }
                     Expression::Cast {
                        cast_type: CastType::Transmute,
                        target_type,
                        expr,
                     } => {
                        let val = expr_to_val(*expr, ctx);
                        match (ctx.ast.expressions[*expr].exp_type.as_ref().unwrap(), target_type) {
                           (&I16_TYPE, &U16_TYPE) => {
                              format!("and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111)
                           }
                           (&I8_TYPE, &U8_TYPE) => {
                              format!("and {}, {}", val, 0b0000_0000_0000_0000_0000_0000_1111_1111)
                           }
                           (&U16_TYPE, &I16_TYPE) => {
                              format!("extsh {}", val)
                           }
                           (&U8_TYPE, &I8_TYPE) => {
                              format!("extsb {}", val)
                           }
                           (ExpressionType::Float(_), ExpressionType::Int(_))
                           | (ExpressionType::Int(_), ExpressionType::Float(_)) => {
                              format!("cast {}", val)
                           }
                           _ => format!("copy {}", val),
                        }
                     }
                     _ => unreachable!(),
                  }
               };

               writeln!(
                  ctx.buf,
                  "   %r{} ={} {}",
                  reg,
                  roland_type_to_base_type(rhs_expr_node.exp_type.as_ref().unwrap()),
                  rhs_expr,
               )
               .unwrap();
            }
         }
         CfgInstruction::Expression(en) => match &ctx.ast.expressions[*en].expression {
            Expression::ProcedureCall { proc_expr, args } => {
               writeln!(ctx.buf, "   {}", make_call_expr(*proc_expr, args, ctx)).unwrap();
            }
            _ => debug_assert!(!expression_could_have_side_effects(*en, &ctx.ast.expressions)),
         },
         CfgInstruction::Return(en) => {
            debug_assert!(!expression_could_have_side_effects(*en, &ctx.ast.expressions));
            if *ctx.ast.expressions[*en].exp_type.as_ref().unwrap() == ExpressionType::Never {
               writeln!(&mut ctx.buf, "   hlt").unwrap();
            } else if sizeof_type_mem(
               ctx.ast.expressions[*en].exp_type.as_ref().unwrap(),
               ctx.udt,
               BaseTarget::Qbe,
            ) == 0
            {
               writeln!(&mut ctx.buf, "   ret").unwrap();
            } else {
               let val = expr_to_val(*en, ctx);
               writeln!(&mut ctx.buf, "   ret {}", val).unwrap();
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

fn mangle<'a>(proc_id: ProcedureId, proc: &ProcedureNode, interner: &'a Interner) -> Cow<'a, str> {
   let proc_name = interner.lookup(proc.definition.name.str);
   if proc.impl_source != ProcImplSource::Native || proc_name == "main" {
      // builtin procedures can't be monomorphized and thus don't need to be mangled
      // external procedures mustn't be mangled, for obvious reasons
      // TODO: we should still quote external identifiers in case they have unicode
      return Cow::Borrowed(proc_name);
   }
   let mut full_str = format!(".{}_{}", proc_id.data().as_ffi(), proc_name).into_bytes();

   // The QBE max char length is 80 minutes the two quotes = 78
   // ... and minus one more for reasons I don't understand, but is empirically necessary
   full_str.truncate(77);
   // we may have just truncated a unicode character. let's fix it up:
   // (this is incredibly lazy. it truncates all non single-byte utf-8 characters)
   // (TODO: a more sophisticated algorithm that removes trailing broken char only)
   while (full_str.last().unwrap() & 0x80) != 0 {
      full_str.pop();
   }

   // 77 above plus 2 quotes = 79
   let mut final_string = String::with_capacity(79);
   final_string.push('"');
   if cfg!(debug_assertions) {
      final_string.push_str(str::from_utf8(&full_str).unwrap());
   } else {
      // safety: above algorithm ensures that after truncating we remove any invalid unicode bytes
      // we do it this way to avoid examining the whole string
      unsafe {
         final_string.push_str(str::from_utf8_unchecked(&full_str));
      }
   }
   final_string.push('"');

   Cow::Owned(final_string)
}

// TODO: rework this to write directly into bytestream or otherwise not allocate
fn expr_to_val(expr_index: ExpressionId, ctx: &GenerationContext) -> String {
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
      Expression::FloatLiteral(v) => match *expr_node.exp_type.as_ref().unwrap() {
         F64_TYPE => format!("d_{}", v),
         F32_TYPE => format!("s_{}", v),
         _ => unreachable!(),
      },
      Expression::BoolLiteral(val) => {
         format!("{}", u8::from(*val))
      }
      Expression::UnaryOperator(UnOp::Dereference, inner) => {
         if let Expression::Variable(v) = ctx.ast.expressions[*inner].expression {
            match ctx.var_to_slot.get(&v) {
               Some(VarSlot::Register(reg)) => {
                  format!("%r{}", reg)
               }
               // TODO: justify why producing an address is OK here
               Some(VarSlot::Stack(v)) => {
                  format!("%v{}", v)
               }
               None => {
                  // global
                  format!("$.v{}", v.0)
               }
            }
         } else {
            unreachable!()
         }
      }
      Expression::Variable(v) => {
         match ctx.var_to_slot.get(v) {
            Some(VarSlot::Register(reg)) => {
               // TODO this should not be reachable?
               format!("%r{}", reg)
            }
            Some(VarSlot::Stack(v)) => {
               format!("%v{}", v)
            }
            None => {
               // global
               format!("$.v{}", v.0)
            }
         }
      }
      Expression::StringLiteral(id) => {
         format!("$.s{}", ctx.string_literals.get_index_of(id).unwrap())
      }
      Expression::BoundFcnLiteral(proc_id, _) => {
         format!("${}", mangle(*proc_id, &ctx.procedures[*proc_id], ctx.interner))
      }
      _ => unreachable!(),
   }
}

#[must_use]
fn make_load(load_target: &str, a_type: &ExpressionType) -> String {
   match a_type {
      ExpressionType::Bool | &U8_TYPE => {
         format!("loadub {}", load_target)
      }
      &I8_TYPE => {
         format!("loadsb {}", load_target)
      }
      &U16_TYPE => {
         format!("loaduh {}", load_target)
      }
      &I16_TYPE => {
         format!("loadsh {}", load_target)
      }
      &U32_TYPE => {
         format!("loaduw {}", load_target)
      }
      &I32_TYPE => {
         format!("loadsw {}", load_target)
      }
      &U64_TYPE | &I64_TYPE | ExpressionType::ProcedurePointer { .. } => {
         format!("loadl {}", load_target)
      }
      &F32_TYPE => {
         format!("loads {}", load_target)
      }
      &F64_TYPE => {
         format!("loadd {}", load_target)
      }
      _ => unreachable!(),
   }
}

#[must_use]
fn make_call_expr(proc_expr: ExpressionId, args: &[ArgumentNode], ctx: &GenerationContext) -> String {
   use std::fmt::Write;

   let mut s = String::new();
   match ctx.ast.expressions[proc_expr].exp_type.as_ref().unwrap() {
      ExpressionType::ProcedureItem(id, _) => {
         write!(&mut s, "call ${}(", mangle(*id, &ctx.procedures[*id], ctx.interner)).unwrap();
      }
      ExpressionType::ProcedurePointer { .. } => {
         let val = expr_to_val(proc_expr, ctx);
         write!(&mut s, "call {}(", val).unwrap();
      }
      _ => unreachable!(),
   }
   for arg in args.iter() {
      if let Some(arg_type) = roland_type_to_abi_type(
         ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap(),
         ctx.udt,
         &ctx.aggregate_defs,
      ) {
         let val = expr_to_val(arg.expr, ctx);
         write!(&mut s, "{} {}, ", arg_type, val).unwrap();
      }
   }
   write!(&mut s, ")").unwrap();
   s
}
