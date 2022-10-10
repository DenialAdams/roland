use indexmap::IndexMap;

use crate::parse::{BlockNode, CastType, Expression, ExpressionId, ExpressionPool, Program, Statement, VariableId};
use crate::type_data::{ExpressionType, IntWidth, ValueType};

pub fn is_wasm_compatible_rval_transmute(source_type: &ExpressionType, target_type: &ExpressionType) -> bool {
   match (source_type, &target_type) {
      (ExpressionType::Pointer(_, _), ExpressionType::Pointer(_, _)) => true,
      (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Pointer(_, _)) if x.width == IntWidth::Pointer => true,
      (ExpressionType::Pointer(_, _), ExpressionType::Value(ValueType::Int(x))) if x.width == IntWidth::Pointer => true,
      (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Int(y))) => {
         x.width.as_num_bytes() == y.width.as_num_bytes()
      }
      (ExpressionType::Value(ValueType::Float(x)), ExpressionType::Value(ValueType::Int(y))) => {
         x.width.as_num_bytes() == y.width.as_num_bytes()
      }
      (ExpressionType::Value(ValueType::Int(x)), ExpressionType::Value(ValueType::Float(y))) => {
         x.width.as_num_bytes() == y.width.as_num_bytes()
      }
      _ => false,
   }
}

struct VvContext<'a, 'b> {
   expressions: &'a ExpressionPool,
   virtual_vars: IndexMap<ExpressionId, VariableId>,
   cur_procedure_locals: &'b mut IndexMap<VariableId, ExpressionType>,
   next_variable: VariableId,
}

impl VvContext<'_, '_> {
   fn declare_vv(&mut self, expr_id: ExpressionId) {
      let var_id = self.next_variable;
      self.next_variable = self.next_variable.next();
      self
         .cur_procedure_locals
         .insert(var_id, self.expressions[expr_id].exp_type.clone().unwrap());
      self.virtual_vars.insert(expr_id, var_id);
   }
}

pub fn add_virtual_vars(program: &mut Program, expressions: &ExpressionPool) {
   let mut vv_context = VvContext {
      expressions,
      virtual_vars: IndexMap::new(),
      cur_procedure_locals: &mut IndexMap::new(),
      next_variable: program.next_variable,
   };

   for procedure in program.procedures.iter_mut() {
      vv_context.cur_procedure_locals = &mut procedure.locals;
      vv_block(&mut procedure.block, &mut vv_context);

      debug_assert!(procedure.virtual_locals.is_empty());
      std::mem::swap(&mut procedure.virtual_locals, &mut vv_context.virtual_vars);
   }

   program.next_variable = vv_context.next_variable;
}

fn vv_block(block: &mut BlockNode, vv_context: &mut VvContext) {
   for statement in block.statements.iter_mut() {
      vv_statement(&mut statement.statement, vv_context);
   }
}

fn vv_statement(statement: &mut Statement, vv_context: &mut VvContext) {
   match statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         vv_expr(*lhs_expr, vv_context);
         vv_expr(*rhs_expr, vv_context);
      }
      Statement::Block(block) => {
         vv_block(block, vv_context);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse(if_expr, if_block, else_statement) => {
         vv_expr(*if_expr, vv_context);
         vv_block(if_block, vv_context);
         vv_statement(&mut else_statement.statement, vv_context);
      }
      Statement::For(_var, start, end, block, _, _) => {
         vv_expr(*start, vv_context);
         vv_expr(*end, vv_context);
         vv_block(block, vv_context);

         // This virtual variable will be used to hoist the end expression out of the loop
         vv_context.declare_vv(*end);
      }
      Statement::Loop(block) => {
         vv_block(block, vv_context);
      }
      Statement::Expression(expr) => {
         vv_expr(*expr, vv_context);
      }
      Statement::Return(expr) => {
         vv_expr(*expr, vv_context);
      }
      Statement::VariableDeclaration(_, expr, _, _) => {
         vv_expr(*expr, vv_context);
      }
   }
}

fn vv_expr(expr_index: ExpressionId, vv_context: &mut VvContext) {
   match &vv_context.expressions[expr_index].expression {
      Expression::ArrayIndex { array, index } => {
         vv_expr(*array, vv_context);
         vv_expr(*index, vv_context);

         let array_expression = &vv_context.expressions[*array];

         // If this is an rvalue, we need to store this array in memory to do the indexing
         // and hence declare a virtual variable here. It's important that this
         // runs after validation, because we need type inference to be complete
         if !array_expression
            .expression
            .is_lvalue_disregard_consts(vv_context.expressions)
         {
            vv_context.declare_vv(*array);
         }
      }
      Expression::ProcedureCall { args, .. } => {
         for arg in args.iter() {
            vv_expr(arg.expr, vv_context);

            if arg.name.is_some() {
               vv_context.declare_vv(arg.expr);
            }
         }
      }
      Expression::BinaryOperator {
         operator: _operator,
         lhs,
         rhs,
      } => {
         vv_expr(*lhs, vv_context);
         vv_expr(*rhs, vv_context);
      }
      Expression::UnaryOperator(_op, expr) => {
         vv_expr(*expr, vv_context);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter() {
            vv_expr(*expr, vv_context);
            vv_context.declare_vv(*expr);
         }
      }
      Expression::FieldAccess(_field_names, expr) => {
         vv_expr(*expr, vv_context);
      }
      Expression::Cast {
         cast_type: CastType::Transmute,
         target_type,
         expr,
      } => {
         vv_expr(*expr, vv_context);

         let e = &vv_context.expressions[*expr];

         if !e.expression.is_lvalue_disregard_consts(vv_context.expressions)
            && !is_wasm_compatible_rval_transmute(e.exp_type.as_ref().unwrap(), target_type)
         {
            vv_context.declare_vv(*expr);
         }
      }
      Expression::Cast { expr, .. } => {
         vv_expr(*expr, vv_context);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            vv_expr(*expr, vv_context);
         }
      }
      Expression::EnumLiteral(_, _) => (),
      Expression::BoolLiteral(_) => (),
      Expression::StringLiteral(_) => (),
      Expression::IntLiteral { .. } => (),
      Expression::FloatLiteral(_) => (),
      Expression::BoundFcnLiteral(_, _) => (),
      Expression::UnitLiteral => (),
      Expression::UnresolvedVariable(_) => unreachable!(),
      Expression::Variable(_) => (),
   }
}
