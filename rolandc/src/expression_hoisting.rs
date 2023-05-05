use indexmap::IndexMap;

use crate::constant_folding::expression_could_have_side_effects;
use crate::parse::{
   AstPool, BlockNode, CastType, Expression, ExpressionId, ExpressionNode, ExpressionPool, Program, Statement,
   StatementId, StatementNode, VariableId,
};
use crate::type_data::ExpressionType;

pub fn is_wasm_compatible_rval_transmute(source_type: &ExpressionType, target_type: &ExpressionType) -> bool {
   source_type == target_type
      || matches!(
         (source_type, &target_type),
         (
            ExpressionType::Int(_) | ExpressionType::Float(_),
            ExpressionType::Int(_) | ExpressionType::Float(_)
         )
      )
}

struct VvContext<'a> {
   cur_procedure_locals: &'a mut IndexMap<VariableId, ExpressionType>,
   next_variable: VariableId,
   virtual_vars: Vec<(ExpressionId, VariableId, usize)>,
}

impl VvContext<'_> {
   fn declare_vv(&mut self, expr_id: ExpressionId, expressions: &ExpressionPool, current_stmt: usize) {
      let var_id = self.next_variable;
      self.next_variable = self.next_variable.next();
      self
         .cur_procedure_locals
         .insert(var_id, expressions[expr_id].exp_type.clone().unwrap());
      self.virtual_vars.push((expr_id, var_id, current_stmt));
   }
}

// We hoist for a couple of different reasons:
// 1) Some operations are easier to sequence in the backend when side effects are pulled into separate statements (for loops, procedure calls, struct literals)
// 2) Some operations are easier to implement in the backend when rvalue's dont have to be considered (array indexing, field access, transmute)
// 3) The constant folder can't fold away an entire expression with side effects, but it can if the side effect is pulled out into a separate statement
//    - (this is of particular importance for field access - we need to lower all array length queries (which is pure type system info) before the backend)
pub fn expression_hoisting(program: &mut Program) {
   let mut vv_context = VvContext {
      cur_procedure_locals: &mut IndexMap::new(),
      next_variable: program.next_variable,
      virtual_vars: Vec::new(),
   };

   for procedure in program.procedures.values_mut() {
      vv_context.cur_procedure_locals = &mut procedure.locals;
      vv_block(&mut procedure.block, &mut vv_context, &mut program.ast);
   }

   program.next_variable = vv_context.next_variable;
}

fn vv_block(block: &mut BlockNode, vv_context: &mut VvContext, ast: &mut AstPool) {
   let before_vv_len = vv_context.virtual_vars.len();
   for (current_stmt, statement) in block.statements.iter().copied().enumerate() {
      vv_statement(statement, vv_context, ast, current_stmt);
   }

   for vv in vv_context.virtual_vars.drain(before_vv_len..).rev() {
      let (vv_assignment_stmt, loc) = {
         let et = ast.expressions[vv.0].exp_type.clone();
         let el = ast.expressions[vv.0].location;
         let lhs = ast.expressions.insert(ExpressionNode {
            expression: Expression::Variable(vv.1),
            exp_type: et,
            location: el,
         });
         let rhs = ast.expressions.insert(ast.expressions[vv.0].clone());
         (Statement::Assignment(lhs, rhs), el)
      };

      let new_id = ast.statements.insert(StatementNode {
         statement: vv_assignment_stmt,
         location: loc,
      });
      block.statements.insert(vv.2, new_id);
      ast.expressions[vv.0].expression = Expression::Variable(vv.1);
   }
}

fn vv_statement(statement: StatementId, vv_context: &mut VvContext, ast: &mut AstPool, current_statement: usize) {
   // TODO: dummy stmt?
   let mut the_statement = std::mem::replace(&mut ast.statements[statement].statement, Statement::Break);
   match &mut the_statement {
      Statement::Assignment(lhs_expr, rhs_expr) => {
         vv_expr(*lhs_expr, vv_context, &ast.expressions, current_statement);
         vv_expr(*rhs_expr, vv_context, &ast.expressions, current_statement);
      }
      Statement::Block(block) => {
         vv_block(block, vv_context, ast);
      }
      Statement::Break | Statement::Continue => (),
      Statement::IfElse(if_expr, if_block, else_statement) => {
         vv_expr(*if_expr, vv_context, &ast.expressions, current_statement);
         vv_block(if_block, vv_context, ast);
         vv_statement(*else_statement, vv_context, ast, current_statement);
      }
      Statement::For(_var, start, end, block, _inclusive, start_var_id) => {
         vv_expr(*start, vv_context, &ast.expressions, current_statement);
         vv_expr(*end, vv_context, &ast.expressions, current_statement);
         vv_block(block, vv_context, ast);

         // there is a already a variable id for start, but we still need to hoist
         vv_context.virtual_vars.push((*start, *start_var_id, current_statement));

         // This virtual variable will be used to hoist the end expression out of the loop
         if expression_could_have_side_effects(*end, &ast.expressions) {
            vv_context.declare_vv(*end, &ast.expressions, current_statement);
         }
      }
      Statement::Loop(block) => {
         vv_block(block, vv_context, ast);
      }
      Statement::Defer(_) => unreachable!(),
      Statement::Expression(expr) => {
         vv_expr(*expr, vv_context, &ast.expressions, current_statement);
      }
      Statement::Return(expr) => {
         vv_expr(*expr, vv_context, &ast.expressions, current_statement);
      }
      Statement::VariableDeclaration(_, opt_expr, _, _) => {
         if let Some(expr) = opt_expr {
            vv_expr(*expr, vv_context, &ast.expressions, current_statement);
         }
      }
   }
   ast.statements[statement].statement = the_statement;
}

fn vv_expr(expr_index: ExpressionId, vv_context: &mut VvContext, expressions: &ExpressionPool, current_statement: usize) {
   match &expressions[expr_index].expression {
      Expression::ArrayIndex { array, index } => {
         vv_expr(*array, vv_context, expressions, current_statement);
         vv_expr(*index, vv_context, expressions, current_statement);

         let array_expression = &expressions[*array];

         // If this is an rvalue, we need to store this array in memory to do the indexing
         // and hence declare a virtual variable here. It's important that this
         // runs after validation, because we need type inference to be complete
         if !array_expression.expression.is_lvalue_disregard_consts(expressions) {
            vv_context.declare_vv(*array, expressions, current_statement);
         }
      }
      Expression::ProcedureCall { args, proc_expr } => {
         vv_expr(*proc_expr, vv_context, expressions, current_statement);

         let mut any_named_arg = false;
         for arg in args.iter() {
            vv_expr(arg.expr, vv_context, expressions, current_statement);

            any_named_arg |= arg.name.is_some();
         }

         if any_named_arg {
            for arg in args.iter() {
               if expression_could_have_side_effects(arg.expr, expressions) {
                  vv_context.declare_vv(arg.expr, expressions, current_statement);
               }
            }
         }

         if matches!(
            expressions[*proc_expr].exp_type.as_ref().unwrap(),
            ExpressionType::ProcedurePointer { .. }
         ) && expression_could_have_side_effects(*proc_expr, expressions)
         {
            vv_context.declare_vv(*proc_expr, expressions, current_statement);
         }
      }
      Expression::BinaryOperator {
         operator: _operator,
         lhs,
         rhs,
      } => {
         vv_expr(*lhs, vv_context, expressions, current_statement);
         vv_expr(*rhs, vv_context, expressions, current_statement);
      }
      Expression::UnaryOperator(_op, expr) => {
         vv_expr(*expr, vv_context, expressions, current_statement);
      }
      Expression::StructLiteral(_, field_exprs) => {
         for (_, expr) in field_exprs.iter() {
            vv_expr(*expr, vv_context, expressions, current_statement);
            if expression_could_have_side_effects(*expr, expressions) {
               vv_context.declare_vv(*expr, expressions, current_statement);
            }
         }
      }
      Expression::FieldAccess(_field_names, expr) => {
         vv_expr(*expr, vv_context, expressions, current_statement);

         if !expressions[*expr].expression.is_lvalue_disregard_consts(expressions) {
            vv_context.declare_vv(*expr, expressions, current_statement);
         }
      }
      Expression::Cast {
         cast_type: CastType::Transmute,
         target_type,
         expr,
      } => {
         vv_expr(*expr, vv_context, expressions, current_statement);

         let e = &expressions[*expr];

         if !e.expression.is_lvalue_disregard_consts(expressions)
            && !is_wasm_compatible_rval_transmute(e.exp_type.as_ref().unwrap(), target_type)
         {
            vv_context.declare_vv(*expr, expressions, current_statement);
         }
      }
      Expression::Cast { expr, .. } => {
         vv_expr(*expr, vv_context, expressions, current_statement);
      }
      Expression::ArrayLiteral(exprs) => {
         for expr in exprs.iter() {
            vv_expr(*expr, vv_context, expressions, current_statement);
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
