use std::borrow::Cow;
use std::collections::HashSet;
use std::io::Write;

use indexmap::{IndexMap, IndexSet};
use slotmap::{Key, SlotMap};

use super::linearize::{Cfg, CfgInstruction, CFG_END_NODE, CFG_START_NODE};
use super::regalloc::{RegallocResult, VarSlot};
use crate::constant_folding::expression_could_have_side_effects;
use crate::interner::{Interner, StrId};
use crate::parse::{
   ArgumentNode, AstPool, CastType, Expression, ExpressionId, ProcImplSource, ProcedureId, ProcedureNode, UnOp,
   UserDefinedTypeInfo, VariableId,
};
use crate::semantic_analysis::GlobalInfo;
use crate::size_info::sizeof_type_mem;
use crate::type_data::{
   ExpressionType, FloatType, FloatWidth, IntType, IntWidth, F32_TYPE, F64_TYPE, I16_TYPE, I32_TYPE, I64_TYPE, I8_TYPE,
   U16_TYPE, U32_TYPE, U64_TYPE, U8_TYPE,
};
use crate::{Program, Target};

struct GenerationContext<'a> {
   buf: Vec<u8>,
   var_to_slot: IndexMap<VariableId, VarSlot>,
   ast: &'a AstPool,
   procedures: &'a SlotMap<ProcedureId, ProcedureNode>,
   interner: &'a Interner,
   udt: &'a UserDefinedTypeInfo,
   string_literals: &'a IndexSet<StrId>,
   address_temp: u64,
   global_info: &'a IndexMap<VariableId, GlobalInfo>,
   aggregate_defs: IndexSet<ExpressionType>,
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
      _ => unreachable!(),
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
      _ => roland_type_to_base_type(r_type),
   }
}

fn roland_type_to_abi_type(
   r_type: &ExpressionType,
   udt: &UserDefinedTypeInfo,
   aggregate_defs: &IndexSet<ExpressionType>,
) -> Option<Cow<'static, str>> {
   if sizeof_type_mem(r_type, udt, Target::Qbe) == 0 {
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
      ExpressionType::Struct(_) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":s{}", index))
      }
      ExpressionType::Union(_) => {
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
   if sizeof_type_mem(r_type, udt, Target::Qbe) == 0 {
      return None;
   }
   Some(match r_type {
      ExpressionType::Struct(_) => {
         let index = aggregate_defs.get_index_of(r_type).unwrap();
         Cow::Owned(format!(":s{}", index))
      }
      ExpressionType::Union(_) => {
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
         };
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
               let sz = sizeof_type_mem(&field.1.e_type, ctx.udt, Target::Qbe);
               if sz > 0 {
                  write!(ctx.buf, "z {}, ", sz).unwrap();
               }
            }
            let this_offset = ssi.field_offsets_mem.get(field.0).unwrap();
            let padding_bytes = next_offset - this_offset - sizeof_type_mem(&field.1.e_type, ctx.udt, Target::Qbe);
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

      let index = emitted.insert_full(et.clone()).0;

      if sizeof_type_mem(et, udt, Target::Qbe) == 0 {
         return;
      }

      match et {
         ExpressionType::Struct(sid) => {
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
               let padding_bytes = next_offset - this_offset - sizeof_type_mem(&field.1.e_type, udt, Target::Qbe);
               if padding_bytes > 0 {
                  write!(buf, "b {}, ", padding_bytes).unwrap();
               }
            }
            writeln!(buf, "}}").unwrap();
         }
         ExpressionType::Union(uid) => {
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
      address_temp: 0,
      global_info: &program.global_info,
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

   for a_global in program.global_info.iter() {
      write!(ctx.buf, "data $.v{} = {{ ", a_global.0 .0).unwrap();
      match a_global.1.initializer {
         Some(e) => {
            literal_as_data(e, &mut ctx);
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

      let export_txt = if interner.lookup(procedure.definition.name.str) == "main" {
         "export "
      } else {
         ""
      };
      let abi_ret_type = roland_type_to_abi_type(&procedure.definition.ret_type.e_type, ctx.udt, &ctx.aggregate_defs)
         .unwrap_or_else(|| "".into());
      write!(
         ctx.buf,
         "{}function {} ${}(",
         export_txt,
         abi_ret_type,
         mangle(proc_id, &ctx.procedures[proc_id], ctx.interner)
      )
      .unwrap();
      let mut stack_params = HashSet::new();
      for (p_i, param) in procedure.definition.parameters.iter().enumerate() {
         if let Some(p_type) = roland_type_to_abi_type(&param.p_type.e_type, ctx.udt, &ctx.aggregate_defs) {
            match ctx.var_to_slot.get(&param.var_id) {
               Some(VarSlot::Register(reg)) => {
                  write!(ctx.buf, "{} %r{}, ", p_type, reg).unwrap();
               }
               Some(VarSlot::Stack(v)) => {
                  write!(ctx.buf, "{} %v{}, ", p_type, v).unwrap();
                  stack_params.insert(*v as usize);
               }
               None => {
                  // This parameter was not assigned a slot - this variable MUST be unused
                  // we'll just give it some value
                  write!(ctx.buf, "{} %p{}, ", p_type, p_i).unwrap();
               }
            }
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
         if stack_params.contains(&i) {
            continue;
         }
         writeln!(ctx.buf, "   %v{} =l alloc{} {}", i, alignment, sz,).unwrap();
      }
      emit_bb(cfg, CFG_START_NODE, &mut ctx);
      for bb_id in 2..cfg.bbs.len() {
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
         if ctx.global_info.contains_key(&v) {
            Some(format!("$.v{}", v.0))
         } else {
            match ctx.var_to_slot.get(&v).unwrap() {
               VarSlot::Register(_) => None,
               VarSlot::Stack(v) => Some(format!("%v{}", v)),
            }
         }
      }
      Expression::UnaryOperator(UnOp::Dereference, e) => Some(expr_to_val(e, ctx)),
      Expression::UnaryOperator(UnOp::AddressOf, e) => compute_offset(e, ctx),
      Expression::Cast {
         cast_type: CastType::Transmute,
         expr,
         ..
      } => compute_offset(expr, ctx),
      _ => None,
   }
}

fn emit_bb(cfg: &Cfg, bb: usize, ctx: &mut GenerationContext) {
   writeln!(ctx.buf, "@b{}", bb).unwrap();
   for instr in cfg.bbs[bb].instructions.iter() {
      match instr {
         CfgInstruction::IfElse(_, _, _, _)
         | CfgInstruction::Break
         | CfgInstruction::Continue
         | CfgInstruction::Loop(_, _)
         | CfgInstruction::Nop => (),
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
               }
               (Some(l), None) => {
                  if ctx.ast.expressions[*lid].exp_type.as_ref().unwrap().is_aggregate() {
                     // Must be a call
                     write!(
                        ctx.buf,
                        "   %t ={} ",
                        roland_type_to_abi_type(
                           ctx.ast.expressions[*lid].exp_type.as_ref().unwrap(),
                           ctx.udt,
                           &ctx.aggregate_defs
                        )
                        .unwrap()
                     )
                     .unwrap();
                     write_expr(*en, rhs_mem, ctx);
                     let size = sizeof_type_mem(
                        ctx.ast.expressions[*lid].exp_type.as_ref().unwrap(),
                        ctx.udt,
                        Target::Qbe,
                     );
                     writeln!(ctx.buf, "   blit %t, {}, {}", l, size).unwrap();
                  } else {
                     let suffix = roland_type_to_extended_type(ctx.ast.expressions[*lid].exp_type.as_ref().unwrap());
                     let val = expr_to_val(*en, ctx);
                     writeln!(ctx.buf, "   store{} {}, {}", suffix, val, l).unwrap();
                  }
               }
               _ => {
                  let len = &ctx.ast.expressions[*lid];
                  match len.expression {
                     Expression::Variable(v) => {
                        let Some(VarSlot::Register(reg)) = ctx.var_to_slot.get(&v) else {
                           unreachable!()
                        };
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
            }
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
            if *ctx.ast.expressions[*en].exp_type.as_ref().unwrap() == ExpressionType::Never {
               writeln!(&mut ctx.buf, "   hlt").unwrap();
            } else if sizeof_type_mem(
               ctx.ast.expressions[*en].exp_type.as_ref().unwrap(),
               ctx.udt,
               Target::Qbe,
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
      // "main" implies exported, and builtin procedures can't be monomorphized and thus
      // don't need to be mangled
      return Cow::Borrowed(proc_name);
   }
   Cow::Owned(format!(".{}_{}", proc_id.data().as_ffi(), proc_name))
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
      Expression::FloatLiteral(v) => match *expr_node.exp_type.as_ref().unwrap() {
         F64_TYPE => format!("d_{}", v),
         F32_TYPE => format!("s_{}", v),
         _ => unreachable!(),
      },
      Expression::BoolLiteral(val) => {
         format!("{}", u8::from(*val))
      }
      Expression::Variable(v) => {
         if ctx.global_info.contains_key(v) {
            format!("$.v{}", v.0)
         } else {
            match ctx.var_to_slot.get(v).unwrap() {
               VarSlot::Register(reg) => {
                  format!("%r{}", reg)
               }
               VarSlot::Stack(v) => {
                  format!("%v{}", v)
               }
            }
         }
      }
      Expression::StringLiteral(id) => {
         format!("$.s{}", ctx.string_literals.get_index_of(id).unwrap())
      }
      Expression::BoundFcnLiteral(proc_id, _) => {
         format!("${}", mangle(*proc_id, &ctx.procedures[*proc_id], ctx.interner))
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
         writeln!(ctx.buf, "copy {}", u8::from(*v)).unwrap();
      }
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
      Expression::FloatLiteral(val) => match *ren.exp_type.as_ref().unwrap() {
         F64_TYPE => writeln!(ctx.buf, "copy d_{}", val).unwrap(),
         F32_TYPE => writeln!(ctx.buf, "copy s_{}", val).unwrap(),
         _ => unreachable!(),
      },
      Expression::Variable(v) => {
         if let Some(VarSlot::Register(reg)) = ctx.var_to_slot.get(v) {
            writeln!(ctx.buf, "copy %r{}", reg).unwrap();
         } else {
            emit_load(&mut ctx.buf, &rhs_mem.unwrap(), ren.exp_type.as_ref().unwrap());
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
            writeln!(
               ctx.buf,
               "copy ${}",
               mangle(*proc_id, &ctx.procedures[*proc_id], ctx.interner)
            )
            .unwrap();
         } else {
            writeln!(ctx.buf, "copy {}", rhs_mem.unwrap()).unwrap();
         }
      }
      Expression::UnaryOperator(operator, inner_id) => {
         let inner_val = expr_to_val(*inner_id, ctx);
         match operator {
            crate::parse::UnOp::Negate => writeln!(ctx.buf, "neg {}", inner_val).unwrap(),
            crate::parse::UnOp::Complement => {
               if *ctx.ast.expressions[*inner_id].exp_type.as_ref().unwrap() == ExpressionType::Bool {
                  writeln!(ctx.buf, "ceqw {}, 0", inner_val).unwrap();
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
                  writeln!(ctx.buf, "xor {}, {}", inner_val, magic_const).unwrap();
               }
            }
            crate::parse::UnOp::AddressOf => unreachable!(),
            crate::parse::UnOp::Dereference => emit_load(&mut ctx.buf, &inner_val, ren.exp_type.as_ref().unwrap()),
         }
      }
      Expression::FieldAccess(_, _) | Expression::ArrayIndex { .. } => {
         emit_load(&mut ctx.buf, &rhs_mem.unwrap(), ren.exp_type.as_ref().unwrap());
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
               match (l.width, r.width) {
                  (IntWidth::Eight, IntWidth::Two) => {
                     if r.signed {
                        writeln!(ctx.buf, "extsh {}", val).unwrap();
                     } else {
                        writeln!(ctx.buf, "and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111).unwrap();
                     }
                  }
                  (IntWidth::Eight, IntWidth::One) => {
                     if r.signed {
                        writeln!(ctx.buf, "extsb {}", val).unwrap();
                     } else {
                        writeln!(ctx.buf, "and {}, {}", val, 0b0000_0000_0000_0000_0000_0000_1111_1111).unwrap();
                     }
                  }
                  (IntWidth::Four, IntWidth::Two) => {
                     if r.signed {
                        writeln!(ctx.buf, "extsh {}", val).unwrap();
                     } else {
                        writeln!(ctx.buf, "and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111).unwrap();
                     }
                  }
                  (IntWidth::Four | IntWidth::Two, IntWidth::One) => {
                     if r.signed {
                        writeln!(ctx.buf, "extsb {}", val).unwrap();
                     } else {
                        writeln!(ctx.buf, "and {}, {}", val, 0b0000_0000_0000_0000_0000_0000_1111_1111).unwrap();
                     }
                  }
                  (IntWidth::Two, IntWidth::Two) => {
                     if !l.signed && r.signed {
                        writeln!(ctx.buf, "extsh {}", val).unwrap();
                     } else if l.signed && !r.signed {
                        writeln!(ctx.buf, "and {}, {}", val, 0b0000_0000_0000_0000_1111_1111_1111_1111).unwrap();
                     } else {
                        writeln!(ctx.buf, "copy {}", val).unwrap();
                     }
                  }
                  (IntWidth::One, IntWidth::One) => {
                     if !l.signed && r.signed {
                        writeln!(ctx.buf, "extsb {}", val).unwrap();
                     } else if l.signed && !r.signed {
                        writeln!(ctx.buf, "and {}, {}", val, 0b0000_0000_0000_0000_0000_0000_1111_1111).unwrap();
                     } else {
                        writeln!(ctx.buf, "copy {}", val).unwrap();
                     }
                  }
                  _ => writeln!(ctx.buf, "copy {}", val).unwrap(),
               }
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
            (ExpressionType::Float(FloatType { width: src_width }), ExpressionType::Int(IntType { signed, .. })) => {
               match src_width {
                  FloatWidth::Eight => {
                     if *signed {
                        writeln!(ctx.buf, "dtosi {}", val).unwrap();
                     } else {
                        writeln!(ctx.buf, "dtoui {}", val).unwrap();
                     }
                  }
                  FloatWidth::Four => {
                     if *signed {
                        writeln!(ctx.buf, "stosi {}", val).unwrap();
                     } else {
                        writeln!(ctx.buf, "stoui {}", val).unwrap();
                     }
                  }
               }
            }
            (
               ExpressionType::Int(IntType {
                  signed,
                  width: src_width,
               }),
               ExpressionType::Float(_),
            ) => match (src_width, signed) {
               (IntWidth::Eight, true) => writeln!(ctx.buf, "sltof {}", val).unwrap(),
               (IntWidth::Eight, false) => writeln!(ctx.buf, "ultof {}", val).unwrap(),
               (_, true) => writeln!(ctx.buf, "swtof {}", val).unwrap(),
               (_, false) => writeln!(ctx.buf, "uwtof {}", val).unwrap(),
            },
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
         if let Some(load_target) = rhs_mem {
            emit_load(&mut ctx.buf, &load_target, ren.exp_type.as_ref().unwrap());
         } else {
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
      }
      _ => unreachable!(),
   }
}

fn emit_load(buf: &mut Vec<u8>, load_target: &str, a_type: &ExpressionType) {
   match a_type {
      ExpressionType::Bool | &U8_TYPE => {
         writeln!(buf, "loadub {}", load_target).unwrap();
      }
      &I8_TYPE => {
         writeln!(buf, "loadsb {}", load_target).unwrap();
      }
      &U16_TYPE => {
         writeln!(buf, "loaduh {}", load_target).unwrap();
      }
      &I16_TYPE => {
         writeln!(buf, "loadsh {}", load_target).unwrap();
      }
      &U32_TYPE => {
         writeln!(buf, "loaduw {}", load_target).unwrap();
      }
      &I32_TYPE => {
         writeln!(buf, "loadsw {}", load_target).unwrap();
      }
      &U64_TYPE | &I64_TYPE | ExpressionType::ProcedurePointer { .. } => {
         writeln!(buf, "loadl {}", load_target).unwrap();
      }
      &F32_TYPE => {
         writeln!(buf, "loads {}", load_target).unwrap();
      }
      &F64_TYPE => {
         writeln!(buf, "loads {}", load_target).unwrap();
      }
      _ => unreachable!(),
   }
}

fn write_call_expr(proc_expr: ExpressionId, args: &[ArgumentNode], ctx: &mut GenerationContext) {
   match ctx.ast.expressions[proc_expr].exp_type.as_ref().unwrap() {
      ExpressionType::ProcedureItem(id, _) => {
         write!(ctx.buf, "call ${}(", mangle(*id, &ctx.procedures[*id], ctx.interner)).unwrap();
      }
      ExpressionType::ProcedurePointer { .. } => {
         let val = expr_to_val(proc_expr, ctx);
         write!(ctx.buf, "call {}(", val).unwrap();
      }
      _ => unreachable!(),
   };
   for arg in args.iter() {
      let val = expr_to_val(arg.expr, ctx);
      if let Some(arg_type) = roland_type_to_abi_type(
         ctx.ast.expressions[arg.expr].exp_type.as_ref().unwrap(),
         ctx.udt,
         &ctx.aggregate_defs,
      ) {
         write!(ctx.buf, "{} {}, ", arg_type, val).unwrap();
      }
   }
   writeln!(ctx.buf, ")").unwrap();
}

pub fn replace_main_return_val(program: &mut Program, interner: &Interner) {
   let main_id = program.procedure_name_table[&interner.reverse_lookup("main").unwrap()];
   program.procedures[main_id].definition.ret_type.e_type = ExpressionType::Int(IntType {
      signed: true,
      width: IntWidth::Four,
   });
   for instr in program.procedure_bodies[main_id]
      .cfg
      .bbs
      .iter_mut()
      .flat_map(|x| x.instructions.iter_mut())
   {
      let CfgInstruction::Return(ret_val) = instr else {
         continue;
      };
      program.ast.expressions[*ret_val].expression = Expression::IntLiteral {
         val: 0,
         synthetic: true,
      };
      program.ast.expressions[*ret_val].exp_type = Some(ExpressionType::Int(IntType {
         signed: true,
         width: IntWidth::Four,
      }));
   }
}
