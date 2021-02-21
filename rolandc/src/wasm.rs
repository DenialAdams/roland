use crate::parse::{BinOp, Expression, ExpressionNode, Program, Statement, UnOp};
use crate::type_data::{ExpressionType, IntWidth, ValueType, U32_TYPE};
use std::collections::HashMap;
use std::io::Write;
use indexmap::IndexMap;

struct GenerationContext<'a> {
   out: PrettyWasmWriter,
   literal_offsets: HashMap<String, (u32, u32)>,
   local_offsets_mem: HashMap<String, u32>,
   local_offsets_values: HashMap<String, u32>,
   struct_info: &'a IndexMap<String, HashMap<String, ExpressionType>>,
   struct_size_info: HashMap<String, SizeInfo>,
   struct_field_offsets_locals: HashMap<String, HashMap<String, u32>>,
   sum_sizeof_locals_mem: u32,
   loop_depth: u64,
   loop_counter: u64,
}

struct SizeInfo {
   values_size: u32,
   mem_size: u32,
   wasm_size: u32,
}

struct PrettyWasmWriter {
   out: Vec<u8>,
   depth: usize,
}

impl<'a> PrettyWasmWriter {
   fn close(&mut self) {
      self.depth -= 1;
      self.emit_spaces();
      writeln!(self.out, ")").unwrap();
   }

   fn emit_spaces(&mut self) {
      let num_spaces = self.depth * 2;
      self.out.reserve(num_spaces);
      for _ in 0..num_spaces {
         self.out.push(b' ');
      }
   }

   fn emit_module_start(&mut self) {
      self.emit_spaces();
      writeln!(self.out, "(module").unwrap();
      self.depth += 1;
   }

   fn emit_function_start(&mut self, name: &str, params: &[(String, ExpressionType)], result_type: &ExpressionType, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
      self.emit_spaces();
      write!(self.out, "(func ${}", name).unwrap();
      for param in params.into_iter() {
         self.out.push(b' ');
         write_type_as_params(&param.1, &mut self.out, si);
      }
      self.out.push(b' ');
      write_type_as_result(result_type, &mut self.out, si);
      self.out.push(b'\n');
      self.depth += 1;
   }

   fn emit_block_start(&mut self, label_val: u64) {
      self.emit_spaces();
      writeln!(self.out, "block $b_{}", label_val).unwrap();
      self.depth += 1;
   }

   fn emit_loop_start(&mut self, label_val: u64) {
      self.emit_spaces();
      writeln!(self.out, "loop $l_{}", label_val).unwrap();
      self.depth += 1;
   }

   fn emit_end(&mut self) {
      self.depth -= 1;
      self.emit_spaces();
      writeln!(self.out, "end").unwrap();
   }

   fn emit_if_start(&mut self) {
      self.emit_spaces();
      writeln!(self.out, "(if ").unwrap();
      self.depth += 1;
      self.emit_spaces();
      writeln!(self.out, "(i32.eq").unwrap();
      self.depth += 1;
   }

   fn emit_then_start(&mut self) {
      self.emit_spaces();
      writeln!(self.out, "(then ").unwrap();
      self.depth += 1;
   }

   fn emit_else_start(&mut self) {
      self.emit_spaces();
      writeln!(self.out, "(else ").unwrap();
      self.depth += 1;
   }

   fn emit_constant_sexp(&mut self, sexp: &str) {
      self.emit_spaces();
      writeln!(self.out, "{}", sexp).unwrap();
   }

   fn emit_constant_instruction(&mut self, instr: &str) {
      self.emit_spaces();
      writeln!(self.out, "{}", instr).unwrap();
   }

   fn emit_data(&mut self, mem_index: u32, offset: u32, literal: &str) {
      // TODO: escape literal
      self.emit_spaces();
      writeln!(
         &mut self.out,
         "(data {} (i32.const {}) \"{}\")",
         mem_index, offset, literal
      )
      .unwrap();
   }

   fn emit_get_local(&mut self, local_index: u32) {
      self.emit_spaces();
      writeln!(&mut self.out, "local.get {}", local_index).unwrap();
   }

   fn emit_set_global(&mut self, global_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "global.set ${}", global_name).unwrap();
   }

   fn emit_get_global(&mut self, global_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "global.get ${}", global_name).unwrap();
   }

   fn emit_call(&mut self, func_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "call ${}", func_name).unwrap();
   }

   fn emit_const_i32(&mut self, value: u32) {
      self.emit_spaces();
      writeln!(&mut self.out, "i32.const {}", value).unwrap();
   }
}

fn write_type_as_result(e: &ExpressionType, out: &mut Vec<u8>, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
   match e {
      ExpressionType::Value(x) => write_value_type_as_result(x, out, si),
      ExpressionType::Pointer(_, _) => write!(out, "(result i32)").unwrap(),
   }
}

fn write_value_type_as_result(e: &ValueType, out: &mut Vec<u8>, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
   match e {
      ValueType::UnknownInt => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => write!(out, "(result i64)").unwrap(),
         _ => write!(out, "(result i32)").unwrap(),
      },
      ValueType::Bool => write!(out, "(result i32)").unwrap(),
      ValueType::String => write!(out, "(result i32) (result i32)").unwrap(),
      ValueType::Unit => (),
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => for e_type in si.get(x).unwrap().values() {
         write_type_as_result(e_type, out, si);
         out.push(b' ');
      },
   }
}

fn write_type_as_params(e: &ExpressionType, out: &mut Vec<u8>, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
   match e {
      ExpressionType::Value(x) => write_value_type_as_params(x, out, si),
      ExpressionType::Pointer(_, _) => write!(out, "(param i32)").unwrap(),
   }
}

fn write_value_type_as_params(e: &ValueType, out: &mut Vec<u8>, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
   match e {
      ValueType::UnknownInt => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => write!(out, "(param i64)").unwrap(),
         _ => write!(out, "(param i32)").unwrap(),
      },
      ValueType::Bool => write!(out, "(param i32)").unwrap(),
      ValueType::String => write!(out, "(param i32) (param i32)").unwrap(),
      ValueType::Unit => (),
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => for e_type in si.get(x).unwrap().values() {
         write_type_as_params(e_type, out, si);
         out.push(b' ');
      },
   }
}

fn type_to_s(e: &ExpressionType, out: &mut Vec<u8>, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
   match e {
      ExpressionType::Value(x) => value_type_to_s(x, out, si),
      ExpressionType::Pointer(_, _) => write!(out, "i32").unwrap(),
   }
}

fn value_type_to_s(e: &ValueType, out: &mut Vec<u8>, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
   match e {
      ValueType::UnknownInt => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => write!(out, "i64").unwrap(),
         _ => write!(out, "i32").unwrap(),
      },
      ValueType::Bool => write!(out, "i32").unwrap(),
      ValueType::String => write!(out, "i32 i32").unwrap(),
      ValueType::Unit => unreachable!(),
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => for e_type in si.get(x).unwrap().values() {
         type_to_s(e_type, out, si);
         out.push(b' ');
      },
   }
}

/// The size of a type as it's stored in memory
fn sizeof_type_mem(e: &ExpressionType, si: &HashMap<String, SizeInfo>) -> u32 {
   match e {
      ExpressionType::Value(x) => sizeof_value_type_mem(x, si),
      ExpressionType::Pointer(_, _) => 4,
   }
}

fn sizeof_value_type_mem(e: &ValueType, si: &HashMap<String, SizeInfo>) -> u32 {
   match e {
      ValueType::UnknownInt => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         IntWidth::Four => 4,
         IntWidth::Two => 2,
         IntWidth::One => 1,
      },
      ValueType::Bool => 4,
      ValueType::String => 8,
      ValueType::Unit => 0,
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => si.get(x).unwrap().mem_size,
   }
}

/// The size of a type, in number of WASM values
fn sizeof_type_values(e: &ExpressionType, si: &HashMap<String, SizeInfo>) -> u32 {
   match e {
      ExpressionType::Value(x) => sizeof_value_type_values(x, si),
      ExpressionType::Pointer(_, _) => 1,
   }
}

fn sizeof_value_type_values(e: &ValueType, si: &HashMap<String, SizeInfo>) -> u32 {
   match e {
      ValueType::UnknownInt => unreachable!(),
      ValueType::Int(_) => 1,
      ValueType::Bool => 1,
      ValueType::String => 2,
      ValueType::Unit => 0,
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => si.get(x).unwrap().values_size,
   }
}

/// The size of a type, in bytes, as it's stored in locals (minimum size 4 bytes)
fn sizeof_type_wasm(e: &ExpressionType, si: &HashMap<String, SizeInfo>) -> u32 {
   match e {
      ExpressionType::Value(x) => sizeof_value_type_wasm(x, si),
      ExpressionType::Pointer(_, _) => 4,
   }
}

fn sizeof_value_type_wasm(e: &ValueType, si: &HashMap<String, SizeInfo>) -> u32 {
   match e {
      ValueType::UnknownInt => unreachable!(),
      ValueType::Int(x) => match x.width {
         IntWidth::Eight => 8,
         _ => 4,
      },
      ValueType::Bool => 4,
      ValueType::String => 8,
      ValueType::Unit => 0,
      ValueType::CompileError => unreachable!(),
      ValueType::Struct(x) => si.get(x).unwrap().wasm_size,
   }
}

fn calculate_struct_size_info(name: &str, struct_info: &IndexMap<String, HashMap<String, ExpressionType>>, struct_size_info: &mut HashMap<String, SizeInfo>) {
   let mut sum_mem = 0;
   let mut sum_wasm = 0;
   let mut sum_values = 0;
   for field_t in struct_info.get(name).unwrap().values() {
      if let ExpressionType::Value(ValueType::Struct(s)) = field_t {
         if !struct_size_info.contains_key(s) {
            calculate_struct_size_info(s.as_str(), struct_info, struct_size_info);
         }
      }

      // todo: Check this?
      sum_mem += sizeof_type_mem(field_t, struct_size_info);
      sum_wasm += sizeof_type_wasm(field_t, struct_size_info);
      sum_values += sizeof_type_values(field_t, struct_size_info);
   }
   struct_size_info.insert(name.to_owned(), SizeInfo {
      mem_size: sum_mem,
      wasm_size: sum_wasm,
      values_size: sum_values,
   });
}

pub fn emit_wasm(program: &Program) -> Vec<u8> {
   let mut struct_size_info: HashMap<String, SizeInfo> = HashMap::with_capacity(program.struct_info.len());
   for s in program.struct_info.iter() {
      calculate_struct_size_info(s.0.as_str(), &program.struct_info, &mut struct_size_info);
   }

   let mut struct_field_offsets_values: HashMap<String, HashMap<String, u32>> = HashMap::with_capacity(program.struct_info.len());
   for s in program.struct_info.iter() {
      calculate_struct_size_info(s.0.as_str(), &program.struct_info, &mut struct_size_info);

      let mut field_offsets = HashMap::with_capacity(s.1.len());
      let mut offset = 0;
      for field in s.1.iter() {
         field_offsets.insert(field.0.to_string(), offset);
         offset += sizeof_type_values(field.1, &struct_size_info);
      }

      struct_field_offsets_values.insert(s.0.to_string(), field_offsets);
   }


   let mut generation_context = GenerationContext {
      out: PrettyWasmWriter {
         out: Vec::new(),
         depth: 0,
      },
      // todo: just reuse the same map?
      literal_offsets: HashMap::with_capacity(program.literals.len()),
      local_offsets_mem: HashMap::new(),
      local_offsets_values: HashMap::new(),
      struct_info: &program.struct_info,
      struct_size_info,
      struct_field_offsets_locals: struct_field_offsets_values,
      sum_sizeof_locals_mem: 0,
      loop_counter: 0,
      loop_depth: 0,
   };

   generation_context.out.emit_module_start();
   generation_context.out.emit_constant_sexp(
      "(import \"wasi_unstable\" \"fd_write\" (func $fd_write (param i32 i32 i32 i32) (result i32)))",
   );
   generation_context.out.emit_constant_sexp("(memory 1)");
   generation_context
      .out
      .emit_constant_sexp("(export \"memory\" (memory 0))");

   // Data section

   let mut offset: u32 = 16;
   for s in std::iter::once("\\n").chain(program.literals.iter().map(|x| x.as_str())) {
      generation_context.out.emit_data(0, offset, s);
      //TODO: and here truncation
      let s_len = s.len() as u32;
      // TODO: interning to make clone cheap
      generation_context
         .literal_offsets
         .insert(s.to_string(), (offset, s_len));
      // TODO: check for overflow here
      offset += s_len;
   }

   generation_context.out.emit_spaces();
   writeln!(
      generation_context.out.out,
      "(global $sp (mut i32) (i32.const {}))",
      offset
   )
   .unwrap();
   generation_context.out.emit_spaces();
   writeln!(
      generation_context.out.out,
      "(global $bp (mut i32) (i32.const {}))",
      offset
   )
   .unwrap();

   // print
   generation_context
      .out
      .emit_function_start("print", &[("str_offset".into(), ExpressionType::Value(U32_TYPE)), ("str_len".into(), ExpressionType::Value(U32_TYPE))], &ExpressionType::Value(ValueType::Unit), &program.struct_info);
   // build the iovecs array
   generation_context
      .out
      .emit_constant_sexp("(i32.store (i32.const 0) (local.get 0))");
   generation_context
      .out
      .emit_constant_sexp("(i32.store (i32.const 4) (local.get 1))");
   generation_context
      .out
      .emit_constant_sexp("(i32.store (i32.const 8) (i32.const 16))");
   generation_context
      .out
      .emit_constant_sexp("(i32.store (i32.const 12) (i32.const 1))");
   generation_context
      .out
      .emit_constant_sexp("(call $fd_write (i32.const 1) (i32.const 0) (i32.const 2) (i32.const 0))");
   generation_context.out.emit_constant_instruction("drop");
   generation_context.out.close();

   // for every struct + field combo
   // let's emit a function which takes the struct in and outputs the values that make up the field
   // oh boy

   for procedure in program.procedures.iter() {
      generation_context.local_offsets_mem.clear();
      generation_context.local_offsets_values.clear();

      // 0-4 == value of previous frame base pointer
      generation_context.sum_sizeof_locals_mem = 4;

      let mut sum_sizeof_locals_values: u32 = 0;

      for local in procedure.locals.iter() {
         // TODO: interning.
         generation_context
            .local_offsets_mem
            .insert(local.0.clone(), generation_context.sum_sizeof_locals_mem);

         generation_context
            .local_offsets_values
            .insert(local.0.clone(), sum_sizeof_locals_values);

         // TODO: should we check for overflow on this value?
         generation_context.sum_sizeof_locals_mem += sizeof_type_mem(&local.1, &generation_context.struct_size_info);
         // TODO: should we check for overflow on this value?
         sum_sizeof_locals_values += sizeof_type_values(&local.1, &generation_context.struct_size_info);
      }

      generation_context.out.emit_function_start(
         &procedure.name,
         &procedure
            .parameters,
         &procedure.ret_type,
         &program.struct_info,
      );

      if procedure.name == "main" {
         generation_context.out.emit_constant_sexp("(export \"_start\")");
      }

      adjust_stack_function_entry(&mut generation_context);

      // Copy parameters to stack memory so we can take pointers
      for param in &procedure.parameters {
         if sizeof_type_mem(&param.1, &generation_context.struct_size_info) == 0 {
            continue;
         }
         get_stack_address_of_local(&param.0, &mut generation_context);
         generation_context.out.emit_get_local(*generation_context.local_offsets_values.get(param.0.as_str()).unwrap());
         store(&param.1, &mut generation_context);
      }

      for statement in &procedure.block.statements {
         emit_statement(statement, &mut generation_context);
      }

      if let Some(Statement::ReturnStatement(_)) = procedure.block.statements.last() {
         // No need to adjust stack; it was done in the return statement
      } else {
         adjust_stack_function_exit(&mut generation_context);
      }

      generation_context.out.close();
   }

   generation_context.out.close();

   generation_context.out.out
}

fn emit_statement(statement: &Statement, generation_context: &mut GenerationContext) {
   match statement {
      Statement::AssignmentStatement(len, en) => {
         do_emit(len, generation_context);
         do_emit_and_load_lval(en, generation_context);
         let val_type = en.exp_type.as_ref().unwrap();
         store(val_type, generation_context);
      }
      Statement::VariableDeclaration(id, en, _) => {
         get_stack_address_of_local(id, generation_context);
         do_emit_and_load_lval(en, generation_context);
         let val_type = en.exp_type.as_ref().unwrap();
         store(val_type, generation_context);
      }
      Statement::BlockStatement(bn) => {
         for statement in &bn.statements {
            emit_statement(statement, generation_context)
         }
      }
      Statement::LoopStatement(bn) => {
         generation_context.loop_depth += 1;
         generation_context.out.emit_block_start(generation_context.loop_counter);
         generation_context.out.emit_loop_start(generation_context.loop_counter);
         generation_context.loop_counter += 1;
         for statement in &bn.statements {
            emit_statement(statement, generation_context)
         }
         generation_context.out.emit_spaces();
         writeln!(
            generation_context.out.out,
            "br $l_{}",
            generation_context.loop_counter - generation_context.loop_depth
         )
         .unwrap();
         generation_context.out.emit_end();
         generation_context.out.emit_end();
         generation_context.loop_depth -= 1;
      }
      Statement::BreakStatement => {
         generation_context.out.emit_spaces();
         writeln!(
            generation_context.out.out,
            "br $b_{}",
            generation_context.loop_counter - generation_context.loop_depth
         )
         .unwrap();
      }
      Statement::ContinueStatement => {
         generation_context.out.emit_spaces();
         writeln!(
            generation_context.out.out,
            "br $l_{}",
            generation_context.loop_counter - generation_context.loop_depth
         )
         .unwrap();
      }
      Statement::ExpressionStatement(en) => {
         do_emit(en, generation_context);
         for _ in 0..sizeof_type_values(en.exp_type.as_ref().unwrap(), &generation_context.struct_size_info) {
            generation_context.out.emit_constant_instruction("drop");
         }
      }
      Statement::IfElseStatement(en, block_1, block_2) => {
         generation_context.out.emit_if_start();
         // expression
         do_emit_and_load_lval(en, generation_context);
         generation_context.out.emit_constant_instruction("i32.const 1");
         generation_context.out.close();
         // then
         generation_context.out.emit_then_start();
         for statement in &block_1.statements {
            emit_statement(statement, generation_context);
         }
         generation_context.out.close();
         // else
         generation_context.out.emit_else_start();
         emit_statement(block_2, generation_context);
         generation_context.out.close();
         // finish if
         generation_context.out.close();
      }
      Statement::ReturnStatement(en) => {
         do_emit_and_load_lval(en, generation_context);

         adjust_stack_function_exit(generation_context);
         generation_context.out.emit_constant_instruction("return");
      }
   }
}

fn do_emit_and_load_lval(expr_node: &ExpressionNode, generation_context: &mut GenerationContext) {
   do_emit(expr_node, generation_context);

   if expr_node.expression.is_lvalue() {
      load(expr_node.exp_type.as_ref().unwrap(), generation_context, &generation_context.struct_info)
   }
}

fn do_emit(expr_node: &ExpressionNode, generation_context: &mut GenerationContext) {
   match &expr_node.expression {
      Expression::UnitLiteral => (),
      Expression::BoolLiteral(x) => {
         generation_context.out.emit_const_i32(*x as u32);
      }
      Expression::IntLiteral(x) => {
         let wasm_type = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => match x.width {
               IntWidth::Eight => "i64",
               _ => "i32",
            },
            _ => unreachable!(),
         };
         generation_context.out.emit_spaces();
         writeln!(generation_context.out.out, "{}.const {}", wasm_type, x).unwrap();
      }
      Expression::StringLiteral(str) => {
         let (offset, len) = generation_context.literal_offsets.get(str).unwrap();
         generation_context.out.emit_const_i32(*offset);
         generation_context.out.emit_const_i32(*len);
      }
      Expression::BinaryOperator(bin_op, e) => {
         do_emit_and_load_lval(&e.0, generation_context);

         do_emit_and_load_lval(&e.1, generation_context);

         let (wasm_type, suffix) = match e.0.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => {
               let wasm_type = match x.width {
                  IntWidth::Eight => "i64",
                  _ => "i32",
               };
               let suffix = if x.signed { "_s" } else { "_u" };
               (wasm_type, suffix)
            }
            ExpressionType::Value(ValueType::Bool) => ("i32", "_u"),
            _ => unreachable!(),
         };
         generation_context.out.emit_spaces();
         match bin_op {
            BinOp::Add => {
               writeln!(generation_context.out.out, "{}.add", wasm_type).unwrap();
            }
            BinOp::Subtract => {
               writeln!(generation_context.out.out, "{}.sub", wasm_type).unwrap();
            }
            BinOp::Multiply => {
               writeln!(generation_context.out.out, "{}.mul", wasm_type).unwrap();
            }
            BinOp::Divide => {
               writeln!(generation_context.out.out, "{}.div{}", wasm_type, suffix).unwrap();
            }
            BinOp::Equality => {
               writeln!(generation_context.out.out, "{}.eq", wasm_type).unwrap();
            }
            BinOp::NotEquality => {
               writeln!(generation_context.out.out, "{}.ne", wasm_type).unwrap();
            }
            BinOp::GreaterThan => {
               writeln!(generation_context.out.out, "{}.gt{}", wasm_type, suffix).unwrap();
            }
            BinOp::GreaterThanOrEqualTo => {
               writeln!(generation_context.out.out, "{}.ge{}", wasm_type, suffix).unwrap();
            }
            BinOp::LessThan => {
               writeln!(generation_context.out.out, "{}.lt{}", wasm_type, suffix).unwrap();
            }
            BinOp::LessThanOrEqualTo => {
               writeln!(generation_context.out.out, "{}.le{}", wasm_type, suffix).unwrap();
            }
            BinOp::BitwiseAnd => {
               writeln!(generation_context.out.out, "{}.and", wasm_type).unwrap();
            }
            BinOp::BitwiseOr => {
               writeln!(generation_context.out.out, "{}.or", wasm_type).unwrap();
            }
            BinOp::BitwiseXor => {
               writeln!(generation_context.out.out, "{}.xor", wasm_type).unwrap();
            }
         }
      }
      Expression::UnaryOperator(un_op, e) => {
         let wasm_type = match expr_node.exp_type.as_ref().unwrap() {
            ExpressionType::Value(ValueType::Int(x)) => match x.width {
               IntWidth::Eight => "i64",
               _ => "i32",
            },
            ExpressionType::Value(ValueType::Bool) => "i32",
            ExpressionType::Pointer(_, _) => "i32",
            _ => unreachable!(),
         };

         match un_op {
            UnOp::AddressOf => {
               do_emit(e, generation_context);

               // This operator coaxes the lvalue to an rvalue without a load
            }
            UnOp::Dereference => {
               do_emit(e, generation_context);
               load(expr_node.exp_type.as_ref().unwrap(), generation_context, &generation_context.struct_info);
            }
            UnOp::Complement => {
               do_emit_and_load_lval(e, generation_context);

               if *e.exp_type.as_ref().unwrap() == ExpressionType::Value(ValueType::Bool) {
                  generation_context.out.emit_spaces();
                  writeln!(generation_context.out.out, "{}.eqz", wasm_type).unwrap();
               } else {
                  complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
               }
            }
            UnOp::Negate => {
               do_emit_and_load_lval(e, generation_context);

               complement_val(e.exp_type.as_ref().unwrap(), wasm_type, generation_context);
               generation_context.out.emit_spaces();
               writeln!(generation_context.out.out, "{}.const 1", wasm_type).unwrap();
               generation_context.out.emit_spaces();
               writeln!(generation_context.out.out, "{}.add", wasm_type).unwrap();
            }
         }
      }
      Expression::Variable(id) => {
         get_stack_address_of_local(id, generation_context);
      }
      Expression::ProcedureCall(name, args) => {
         for arg in args {
            do_emit_and_load_lval(arg, generation_context);
         }
         generation_context.out.emit_call(name);
      }
      Expression::StructLiteral(_, fields) => {
         for field in fields.iter() {
            do_emit_and_load_lval(&field.1, generation_context);
         }
      },
      Expression::FieldAccess(field_names, lhs) => {
         unimplemented!();
      },
   }
}

fn complement_val(t_type: &ExpressionType, wasm_type: &str, generation_context: &mut GenerationContext) {
   let magic_const: u64 = match t_type {
      ExpressionType::Value(crate::type_data::U8_TYPE) => std::u8::MAX as u64,
      ExpressionType::Value(crate::type_data::U16_TYPE) => std::u16::MAX as u64,
      ExpressionType::Value(crate::type_data::U32_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::U64_TYPE) => std::u64::MAX,
      ExpressionType::Value(crate::type_data::I8_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::I16_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::I32_TYPE) => std::u32::MAX as u64,
      ExpressionType::Value(crate::type_data::I64_TYPE) => std::u64::MAX,
      _ => unreachable!(),
   };
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "{}.const {}", wasm_type, magic_const).unwrap();
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "{}.xor", wasm_type).unwrap();
}

/// Places the address of given local on the stack
fn get_stack_address_of_local(id: &str, generation_context: &mut GenerationContext) {
   let offset = *generation_context.local_offsets_mem.get(id).unwrap();
   generation_context.out.emit_get_global("bp");
   generation_context.out.emit_const_i32(offset);
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "i32.add").unwrap();
}

fn load(val_type: &ExpressionType, generation_context: &mut GenerationContext, si: &IndexMap<String, HashMap<String, ExpressionType>>) {
   if sizeof_type_mem(val_type, &generation_context.struct_size_info) == 0 {
      // Drop the load address; nothing to load
      generation_context.out.emit_constant_instruction("drop");
   } else if sizeof_type_mem(val_type, &generation_context.struct_size_info) == sizeof_type_wasm(val_type, &generation_context.struct_size_info) {
      generation_context.out.emit_spaces();
      type_to_s(val_type, &mut generation_context.out.out, si);
      writeln!(generation_context.out.out, ".load").unwrap();
   } else {
      let (load_suffx, sign_suffix) = match val_type {
         ExpressionType::Value(ValueType::Int(x)) => {
            let load_suffx = match x.width {
               IntWidth::Eight => "64",
               IntWidth::Four => "32",
               IntWidth::Two => "16",
               IntWidth::One => "8",
            };
            let sign_suffix = if x.signed { "_s" } else { "_u" };
            (load_suffx, sign_suffix)
         }
         ExpressionType::Value(ValueType::Bool) => ("32", "_u"),
         _ => unreachable!(),
      };
      generation_context.out.emit_spaces();
      type_to_s(val_type, &mut generation_context.out.out, si);
      writeln!(
         generation_context.out.out,
         ".load{}{}",
         load_suffx,
         sign_suffix
      )
      .unwrap();
   }
}

fn store(val_type: &ExpressionType, generation_context: &mut GenerationContext) {
   if sizeof_type_mem(val_type, &generation_context.struct_size_info) == 0 {
      // Drop the placement address; nothing to store
      generation_context.out.emit_constant_instruction("drop");
   } else if sizeof_type_mem(val_type, &generation_context.struct_size_info) == sizeof_type_wasm(val_type, &generation_context.struct_size_info) {
      generation_context.out.emit_spaces();
      type_to_s(val_type, &mut generation_context.out.out, &generation_context.struct_info);
      writeln!(generation_context.out.out, ".store").unwrap();
   } else {
      let load_suffx = match val_type {
         ExpressionType::Value(ValueType::Int(x)) => {
            let load_suffx = match x.width {
               IntWidth::Eight => "64",
               IntWidth::Four => "32",
               IntWidth::Two => "16",
               IntWidth::One => "8",
            };
            load_suffx
         }
         ExpressionType::Value(ValueType::Bool) => "32",
         _ => unreachable!(),
      };
      generation_context.out.emit_spaces();
      type_to_s(val_type, &mut generation_context.out.out, &generation_context.struct_info);
      writeln!(
         generation_context.out.out,
         ".store{}",
         load_suffx,
      )
      .unwrap();
   }
}

fn adjust_stack_function_entry(generation_context: &mut GenerationContext) {
   if generation_context.sum_sizeof_locals_mem == 0 {
      return;
   }

   generation_context.out.emit_get_global("sp");
   generation_context.out.emit_get_global("bp");
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "i32.store").unwrap();
   generation_context.out.emit_get_global("sp");
   generation_context.out.emit_set_global("bp");
   adjust_stack(generation_context, "add");
}

fn adjust_stack_function_exit(generation_context: &mut GenerationContext) {
   if generation_context.sum_sizeof_locals_mem == 0 {
      return;
   }

   adjust_stack(generation_context, "sub");
   generation_context.out.emit_get_global("sp");
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "i32.load").unwrap();
   generation_context.out.emit_set_global("bp");
}

fn adjust_stack(generation_context: &mut GenerationContext, instr: &str) {
   generation_context.out.emit_get_global("sp");
   generation_context
      .out
      .emit_const_i32(generation_context.sum_sizeof_locals_mem);
   generation_context.out.emit_spaces();
   writeln!(generation_context.out.out, "i32.{}", instr).unwrap();
   generation_context.out.emit_set_global("sp");
}
