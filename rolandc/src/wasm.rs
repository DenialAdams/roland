use crate::parse::{BinOp, Expression, ExpressionNode, ExpressionType, Program, Statement, UnOp};

struct GenerationContext {
}

pub fn emit_wasm(program: &mut Program) {
   let mut generation_context = GenerationContext {
   };

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
      for statement in procedure.block.statements.iter() {
         match statement {
            Statement::VariableDeclaration(id, en) => {
               do_emit(en, &mut generation_context);
            }
            Statement::ExpressionStatement(en) => {
               do_emit(en, &mut generation_context);
            }
         }
      }
   }
}

fn do_emit(expr_node: &ExpressionNode, generation_context: &mut GenerationContext) {
   match &expr_node.expression {
      Expression::IntLiteral(_) => {
         unimplemented!()
      }
      Expression::StringLiteral(_) => {
         unimplemented!()
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
         unimplemented!()
      }
   }
}
