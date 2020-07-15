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

impl PrettyWasmWriter {
   fn close(&mut self) {
      self.out.push(b')');
      self.depth -= 1;
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

   fn emit_constant_sexp(&mut self, sexp: &str) {
      self.emit_spaces();
      writeln!(self.out, "{}", sexp).unwrap();
   }
}

impl Write for PrettyWasmWriter {
   fn write(&mut self, buf: &[u8]) -> Result<usize, std::io::Error> {
      self.out.reserve(buf.len());
      self.out.extend_from_slice(buf);
      Ok(buf.len())
   }

   fn flush(&mut self) -> Result<(), std::io::Error> {
      self.out.flush()
   }
}

fn type_to_s(e: &ExpressionType) -> &'static str {
   match e {
      ExpressionType::Int => "i64",
      ExpressionType::Bool => "i64",
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
      writeln!(&mut generation_context.out, "(data 0 (i32.const {}) \"{}\")", offset, s).unwrap();
      //TODO: and here truncation
      let s_len = s.len() as u32;
      // TODO: interning to make clone cheap
      generation_context.literal_offsets.insert(s.to_string(), (offset, s_len));
      // TODO: check for overflow here
      offset += s_len;
   }

   // Standard Library functions
   // TODO add function bodies
   let standard_lib_procs = [("print_bool", false)];
   for p in standard_lib_procs.iter() {
      writeln!(&mut generation_context.out, "(func ${} nop", p.0).unwrap();
      generation_context.out.indent();
      generation_context.out.close();
   }

   // print
   writeln!(&mut generation_context.out, "(func $print (param $str_offset i32) (param $str_len i32)").unwrap();
   generation_context.out.indent();
   // build the iovecs array
   writeln!(&mut generation_context.out, "(i32.store (i32.const 0) (local.get $str_offset))").unwrap();
   writeln!(&mut generation_context.out, "(i32.store (i32.const 4) (local.get $str_len))").unwrap();
   writeln!(&mut generation_context.out, "(i32.store (i32.const 8) (i32.const 16))").unwrap();
   writeln!(&mut generation_context.out, "(i32.store (i32.const 12) (i32.const 1))").unwrap();
   writeln!(&mut generation_context.out, "(call $fd_write (i32.const 1) (i32.const 0) (i32.const 2) (i32.const 0))").unwrap();
   writeln!(&mut generation_context.out, "drop").unwrap();
   generation_context.out.close();

   // print int
   writeln!(&mut generation_context.out, "(func $print_int (param $int i64)").unwrap();
   generation_context.out.indent();
   // build the iovecs array
   //writeln!(&mut generation_context.out, "(i32.store (i32.const 0) (local.get $str_offset))").unwrap();
   //writeln!(&mut generation_context.out, "(i32.store (i32.const 4) (local.get $str_len))").unwrap();
   writeln!(&mut generation_context.out, "(i32.store (i32.const 8) (i32.const 16))").unwrap();
   writeln!(&mut generation_context.out, "(i32.store (i32.const 12) (i32.const 1))").unwrap();
   writeln!(&mut generation_context.out, "(call $fd_write (i32.const 1) (i32.const 0) (i32.const 2) (i32.const 0))").unwrap();
   writeln!(&mut generation_context.out, "drop").unwrap();
   generation_context.out.close();

   for procedure in program.procedures.iter() {
      writeln!(&mut generation_context.out, "(func ${}", procedure.name).unwrap();
      if procedure.name == "main" {
         writeln!(&mut generation_context.out, "(export \"_start\")").unwrap();
      }
      // TODO params
      // TODO ret type
      generation_context.out.indent();
      for (id, e_type) in procedure.locals.iter() {
         write!(generation_context.out, "(local ${} {}) ", id, type_to_s(e_type)).unwrap();
      }
      writeln!(generation_context.out, "").unwrap();
      for statement in procedure.block.statements.iter() {
         match statement {
            Statement::VariableDeclaration(id, en) => {
               do_emit(en, &mut generation_context);
               writeln!(&mut generation_context.out, "local.set ${}", id).unwrap();
            }
            Statement::ExpressionStatement(en) => {
               do_emit(en, &mut generation_context);
            }
         }
      }
      generation_context.out.close();
   }

   generation_context.out.close();

   generation_context.out.out
}

fn do_emit(expr_node: &ExpressionNode, generation_context: &mut GenerationContext) {
   match &expr_node.expression {
      Expression::IntLiteral(x) => {
         writeln!(&mut generation_context.out, "i64.const {}", x).unwrap();
      }
      Expression::StringLiteral(str) => {
         let (offset, len) = generation_context.literal_offsets.get(str).unwrap();
         writeln!(&mut generation_context.out, "i32.const {}", offset).unwrap();
         writeln!(&mut generation_context.out, "i32.const {}", len).unwrap();
      }
      Expression::BinaryOperator(bin_op, e) => {
         do_emit(&e.0, generation_context);
         do_emit(&e.1, generation_context);
         match bin_op {
            BinOp::Add => {
               writeln!(&mut generation_context.out, "i64.add").unwrap();
            }
            BinOp::Subtract => {
               writeln!(&mut generation_context.out, "i64.sub").unwrap();
            }
            BinOp::Multiply => {
               writeln!(&mut generation_context.out, "i64.mul").unwrap();
            }
            BinOp::Divide => {
               writeln!(&mut generation_context.out, "i64.div_s").unwrap();
            }
            _ => unimplemented!()
         }
      }
      Expression::UnaryOperator(_un_op, _e) => {
         unimplemented!()
      }
      Expression::Variable(id) => {
         writeln!(&mut generation_context.out, "local.get ${}", id).unwrap();
      }
      Expression::ProcedureCall(name, args) => {
         for arg in args {
            do_emit(arg, generation_context);
         }
         writeln!(&mut generation_context.out, "call ${}", name).unwrap();
      }
   }
}
