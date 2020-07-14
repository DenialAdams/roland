use crate::parse::{BinOp, Expression, ExpressionNode, ExpressionType, Program, Statement, UnOp};
use std::io::Write;

struct GenerationContext {
   out: PrettyWasmWriter
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
      }
   };

   writeln!(&mut generation_context.out, "(module").unwrap();
   generation_context.out.indent();


   // Standard Library functions
   // TODO add function bodies
   /*
   let standard_lib_procs = [("print", false), ("print_int", false), ("print_bool", false)];
   for p in standard_lib_procs.iter() {
      validation_context
         .procedure_info
         .insert(p.0.to_string(), ProcedureInfo { pure: p.1 });
   } */

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
      Expression::IntLiteral(_) => {
         unimplemented!()
      }
      Expression::StringLiteral(_) => {
         //unimplemented!()
      }
      Expression::BinaryOperator(bin_op, e) => {
         unimplemented!()
      }
      Expression::UnaryOperator(un_op, e) => {
         unimplemented!()
      }
      Expression::Variable(id) => {
         unimplemented!()
      }
      Expression::ProcedureCall(name, args) => {
         for arg in args {
            do_emit(arg, generation_context);
         }
         writeln!(&mut generation_context.out, "call ${}", name).unwrap();
      }
   }
}
