use crate::parse::{BinOp, Expression, ExpressionNode, ExpressionType, Program, Statement, UnOp};
use std::collections::HashMap;
use std::io::Write;

struct GenerationContext {
   out: PrettyWasmWriter,
   literal_offsets: HashMap<String, (u32, u32)>,
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

   fn emit_function_start<I: IntoIterator<Item=(&'a str, &'a str)>>(&mut self, name: &str, params: I) {
      self.emit_spaces();
      write!(self.out, "(func ${}", name).unwrap();
      for param in params.into_iter() {
         write!(self.out, " (param ${} {})", param.0, param.1).unwrap();
      }
      self.out.push(b'\n');
      self.depth += 1;
   }

   fn emit_if_start(&mut self) {
      self.emit_spaces();
      writeln!(self.out, "(if ").unwrap();
      self.depth += 1;
      self.emit_spaces();
      writeln!(self.out, "(").unwrap();
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
      writeln!(&mut self.out, "(data {} (i32.const {}) \"{}\")", mem_index, offset, literal).unwrap();
   }

   fn emit_local_definition(&mut self, local_name: &str, type_s: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "(local ${} {})", local_name, type_s).unwrap();
   }

   fn emit_set_local(&mut self, local_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "local.set ${}", local_name).unwrap();
   }

   fn emit_get_local(&mut self, local_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "local.get ${}", local_name).unwrap();
   }

   fn emit_call(&mut self, func_name: &str) {
      self.emit_spaces();
      writeln!(&mut self.out, "call ${}", func_name).unwrap();
   }

   fn emit_const_i32(&mut self, value: u32) {
      self.emit_spaces();
      writeln!(&mut self.out, "i32.const {}", value).unwrap();
   }

   fn emit_const_i64(&mut self, value: i64) {
      self.emit_spaces();
      writeln!(&mut self.out, "i64.const {}", value).unwrap();
   }
}

fn type_to_s(e: &ExpressionType) -> &'static str {
   match e {
      ExpressionType::Int => "i64",
      ExpressionType::Bool => "i32",
      ExpressionType::String => unimplemented!(),
      ExpressionType::Unit => unreachable!(),
      ExpressionType::CompileError => unreachable!(),
   }
}

pub fn emit_wasm(program: &Program) -> Vec<u8> {
   let mut generation_context = GenerationContext {
      out: PrettyWasmWriter {
         out: Vec::new(),
         depth: 0,
      },
      // todo: just reuse the same map?
      literal_offsets: HashMap::with_capacity(program.literals.len()),
   };

   generation_context.out.emit_module_start();
   generation_context.out.emit_constant_sexp("(import \"wasi_unstable\" \"fd_write\" (func $fd_write (param i32 i32 i32 i32) (result i32)))");
   generation_context.out.emit_constant_sexp("(memory 1)");
   generation_context.out.emit_constant_sexp("(export \"memory\" (memory 0))");

   // Data section

   let mut offset: u32 = 16;
   for s in std::iter::once("\\n").chain(program.literals.iter().map(|x| x.as_str())) {
      generation_context.out.emit_data(0, offset, s);
      //TODO: and here truncation
      let s_len = s.len() as u32;
      // TODO: interning to make clone cheap
      generation_context.literal_offsets.insert(s.to_string(), (offset, s_len));
      // TODO: check for overflow here
      offset += s_len;
   }

   // print
   // TODO: this shouldnt be vec, but i cant generic
   generation_context.out.emit_function_start("print", vec![("str_offset", "i32"), ("str_len", "i32")]);
   // build the iovecs array
   generation_context.out.emit_constant_sexp("(i32.store (i32.const 0) (local.get $str_offset))");
   generation_context.out.emit_constant_sexp("(i32.store (i32.const 4) (local.get $str_len))");
   generation_context.out.emit_constant_sexp("(i32.store (i32.const 8) (i32.const 16))");
   generation_context.out.emit_constant_sexp("(i32.store (i32.const 12) (i32.const 1))");
   generation_context.out.emit_constant_sexp("(call $fd_write (i32.const 1) (i32.const 0) (i32.const 2) (i32.const 0))");
   generation_context.out.emit_constant_instruction("drop");
   generation_context.out.close();

   // print int
   // TODO: this shouldnt be vec, but i cant generic
   generation_context.out.emit_function_start("print_int", vec![("int", "i64")]);
   // build the iovecs array
   //writeln!(&mut generation_context.out, "(i32.store (i32.const 0) (local.get $str_offset))").unwrap();
   //writeln!(&mut generation_context.out, "(i32.store (i32.const 4) (local.get $str_len))").unwrap();
   generation_context.out.emit_constant_sexp("(i32.store (i32.const 8) (i32.const 16))");
   generation_context.out.emit_constant_sexp("(i32.store (i32.const 12) (i32.const 1))");
   generation_context.out.emit_constant_sexp("(call $fd_write (i32.const 1) (i32.const 0) (i32.const 2) (i32.const 0))");
   generation_context.out.emit_constant_instruction("drop");
   generation_context.out.close();

   for procedure in program.procedures.iter() {
      generation_context.out.emit_function_start(&procedure.name, procedure.parameters.iter().map(|x| (x.0.as_ref(), type_to_s(&x.1))));
      if procedure.name == "main" {
         generation_context.out.emit_constant_sexp("(export \"_start\")");
      }
      // TODO ret type
      for (id, e_type) in procedure.locals.iter() {
         generation_context.out.emit_local_definition(id, type_to_s(e_type));
      }
      emit_statements(&procedure.block.statements, &mut generation_context);
      generation_context.out.close();
   }

   generation_context.out.close();

   generation_context.out.out
}

fn emit_statements(statements: &[Statement], generation_context: &mut GenerationContext) {
   for statement in statements {
      match statement {
         Statement::VariableDeclaration(id, en) => {
            do_emit(en, generation_context);
            generation_context.out.emit_set_local(id);
         }
         Statement::ExpressionStatement(en) => {
            do_emit(en, generation_context);
         }
         Statement::IfElseStatement(en, block_1, block_2) => {
            generation_context.out.emit_if_start();
            // expression
            do_emit(en, generation_context);
            generation_context.out.close();
            // then
            generation_context.out.emit_then_start();
            emit_statements(&block_1.statements, generation_context);
            generation_context.out.close();
            // else
            generation_context.out.emit_else_start();
            emit_statements(&block_2.statements, generation_context);
            generation_context.out.close();
            // finish if
            generation_context.out.close();
         }
      }
   }
}

fn do_emit(expr_node: &ExpressionNode, generation_context: &mut GenerationContext) {
   match &expr_node.expression {
      Expression::BoolLiteral(x) => {
         generation_context.out.emit_const_i32(*x as u32);
      }
      Expression::IntLiteral(x) => {
         generation_context.out.emit_const_i64(*x);
      }
      Expression::StringLiteral(str) => {
         let (offset, len) = generation_context.literal_offsets.get(str).unwrap();
         generation_context.out.emit_const_i32(*offset);
         generation_context.out.emit_const_i32(*len);
      }
      Expression::BinaryOperator(bin_op, e) => {
         do_emit(&e.0, generation_context);
         do_emit(&e.1, generation_context);
         match bin_op {
            BinOp::Add => {
               generation_context.out.emit_constant_instruction("i64.add");
            }
            BinOp::Subtract => {
               generation_context.out.emit_constant_instruction("i64.sub");
            }
            BinOp::Multiply => {
               generation_context.out.emit_constant_instruction("i64.mul");
            }
            BinOp::Divide => {
               generation_context.out.emit_constant_instruction("i64.div_s");
            }
            BinOp::Equality => {
               generation_context.out.emit_constant_instruction("i64.eq");
            }
            BinOp::NotEquality => {
               generation_context.out.emit_constant_instruction("i64.ne");
            }
            BinOp::GreaterThan => {
               generation_context.out.emit_constant_instruction("i64.gt_s");
            }
            BinOp::GreaterThanOrEqualTo => {
               generation_context.out.emit_constant_instruction("i64.ge_s");
            }
            BinOp::LessThan => {
               generation_context.out.emit_constant_instruction("i64.lt_s");
            }
            BinOp::LessThanOrEqualTo => {
               generation_context.out.emit_constant_instruction("i64.le_s");
            }
         }
      }
      Expression::UnaryOperator(un_op, e) => {
         do_emit(e, generation_context);
         match un_op {
            UnOp::LogicalNegate => {
               generation_context.out.emit_constant_instruction("i64.eqz");
            }
            UnOp::Negate => {
               generation_context.out.emit_const_i64(-1); // 0xFF_FF_...
               generation_context.out.emit_constant_instruction("i64.xor");
               generation_context.out.emit_const_i64(1);
               generation_context.out.emit_constant_instruction("i64.add");
            }
         }
      }
      Expression::Variable(id) => {
         generation_context.out.emit_get_local(id);
      }
      Expression::ProcedureCall(name, args) => {
         for arg in args {
            do_emit(arg, generation_context);
         }
         generation_context.out.emit_call(name);
      }
   }
}
