use crate::parse::{BinOp, Expression, ExpressionNode, ExpressionType, Program, Statement, UnOp};
use std::collections::HashMap;
use std::io::Write;

struct GenerationContext {
   out: PrettyWasmWriter,
   literal_offsets: HashMap<String, u32>,
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

   fn indent(&mut self) {
      self.depth += 1;
      let num_spaces = self.depth * 2;
      self.out.reserve(num_spaces);
      for _ in 0..num_spaces {
         self.out.push(b' ');
      }
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

pub fn emit_wasm(program: &Program) -> Vec<u8> {
   let mut generation_context = GenerationContext {
      out: PrettyWasmWriter {
         out: Vec::new(),
         depth: 0,
      },
      // todo: just reuse the same map?
      literal_offsets: HashMap::with_capacity(program.literals.len()),
   };

   writeln!(&mut generation_context.out, "(module").unwrap();
   generation_context.out.indent();

   // Data section

   let mut offset: u32 = 0;
   for s in program.literals.iter() {
      writeln!(&mut generation_context.out, "(data 0 (i32.const {}) \"{}\")", offset, s).unwrap();
      // TODO: interning to make clone cheap
      generation_context.literal_offsets.insert(s.clone(), offset);
      // TODO: check for overflow here
      offset += s.len() as u32;
   }

   // Standard Library functions
   // TODO add function bodies
   let standard_lib_procs = [("print", false), ("print_int", false), ("print_bool", false)];
   for p in standard_lib_procs.iter() {
      // emit body
   }

   for procedure in program.procedures.iter() {
      writeln!(&mut generation_context.out, "(func ${}", procedure.name).unwrap();
      // TODO params
      // TODO ret type
      generation_context.out.indent();
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
      Expression::StringLiteral(_) => {
         //unimplemented!()
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
      Expression::UnaryOperator(un_op, e) => {
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
