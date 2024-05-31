#![warn(clippy::pedantic)]
#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::explicit_iter_loop)] // I find explicit iter more readable
#![allow(clippy::too_many_lines)] // A procedure should have however many lines as it needs. More procedures is not better.
#![allow(clippy::too_many_arguments)] // Similar to above, take the amount that you need
#![allow(clippy::cast_sign_loss)] // I am aware
#![allow(clippy::cast_possible_wrap)] // I am aware
#![allow(clippy::cast_possible_truncation)] // I am aware
#![allow(clippy::missing_errors_doc)] // Nothing is documented
#![allow(clippy::missing_panics_doc)] // Nothing is documented
#![allow(clippy::module_name_repetitions)] // I don't really care that much
#![allow(clippy::new_without_default)] // I don't want dead code
#![allow(clippy::result_unit_err)] // This is based on a notion of public that doesn't really apply for me
#![allow(clippy::needless_bitwise_bool)] // Sometimes I just don't want branches, man

mod backend;
mod compile_consts;
mod constant_folding;
mod dead_code_elimination;
mod defer;
mod disjoint_set;
pub mod error_handling;
mod expression_hoisting;
mod imports;
pub mod interner;
mod lex;
mod logical_op_lowering;
mod loop_lowering;
mod monomorphization;
mod named_argument_lowering;
pub mod parse;
mod pp;
mod pre_backend_lowering;
mod semantic_analysis;
mod size_info;
pub mod source_info;
pub mod type_data;
mod variable_declaration_lowering;

use std::borrow::Cow;
use std::fmt::Display;
use std::path::{Path, PathBuf};

use error_handling::error_handling_macros::rolandc_error;
use error_handling::ErrorManager;
use expression_hoisting::HoistingMode;
use indexmap::{IndexMap, IndexSet};
use interner::Interner;
pub use parse::Program;
use parse::{ImportNode, ProcImplSource, ProcedureId, UserDefinedTypeId};
use semantic_analysis::type_variables::TypeVariableManager;
use semantic_analysis::{definite_assignment, OwnedValidationContext, StorageKind};
use slotmap::SecondaryMap;
use source_info::SourcePath;
use type_data::{ExpressionType, IntWidth};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Target {
   Wasi,
   Wasm4,
   Microw8,
   Lib,
   Qbe,
}

impl Target {
   fn pointer_width(self) -> u8 {
      match self {
         Target::Qbe => 8,
         _ => 4,
      }
   }

   fn lowered_ptr_width(self) -> IntWidth {
      match self {
         Target::Qbe => IntWidth::Eight,
         _ => IntWidth::Four,
      }
   }
}

impl Display for Target {
   fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      match self {
         Target::Wasi => write!(f, "WASI"),
         Target::Wasm4 => write!(f, "WASM-4"),
         Target::Microw8 => write!(f, "Microw8"),
         Target::Lib => write!(f, "lib"),
         Target::Qbe => write!(f, "AMD64"),
      }
   }
}

pub enum CompilationError {
   Lex,
   Parse,
   Semantic,
   Io,
}

pub trait FileResolver<'a> {
   fn resolve_path(&mut self, path: &Path) -> std::io::Result<Cow<'a, str>>;
   const IS_STD: bool = false;
}

pub enum CompilationEntryPoint<'a, FR: FileResolver<'a>> {
   Playground(&'a str),
   PathResolving(PathBuf, FR),
}

// Repeated compilations can be sped up by reusing the context
pub struct CompilationContext {
   pub interner: Interner,
   pub err_manager: ErrorManager,
   pub program: Program,
}

impl CompilationContext {
   #[must_use]
   pub fn new() -> CompilationContext {
      CompilationContext {
         interner: Interner::with_capacity(1024),
         err_manager: ErrorManager::new(),
         program: Program::new(),
      }
   }
}

pub fn compile_for_errors<'a, FR: FileResolver<'a>>(
   ctx: &mut CompilationContext,
   user_program_ep: CompilationEntryPoint<'a, FR>,
   config: &CompilationConfig,
) -> Result<(), CompilationError> {
   ctx.program.clear();
   ctx.err_manager.clear();
   // We don't have to clear the interner - assumption is that the context is coming from a recent version of the same source, so symbols should be relevant

   let std_lib_start_path: PathBuf = match config.target {
      Target::Wasi => "wasi.rol",
      Target::Wasm4 => "wasm4.rol",
      Target::Microw8 => "microw8.rol",
      Target::Lib => "shared.rol",
      Target::Qbe => "amd64.rol",
   }
   .into();

   if config.include_std {
      imports::import_program(ctx, std_lib_start_path, imports::StdFileResolver)?;
   }

   match user_program_ep {
      CompilationEntryPoint::PathResolving(ep_path, resolver) => {
         imports::import_program(ctx, ep_path, resolver)?;
      }
      CompilationEntryPoint::Playground(contents) => {
         let files_to_import = lex_and_parse(
            contents,
            SourcePath::Sandbox,
            &mut ctx.err_manager,
            &mut ctx.interner,
            &mut ctx.program,
         )?;
         if !files_to_import.is_empty() {
            rolandc_error!(
               ctx.err_manager,
               files_to_import[0].location,
               "Can't import files in the Roland playground",
            );
            return Err(CompilationError::Io);
         }
      }
   };

   semantic_analysis::type_and_procedure_info::populate_type_and_procedure_info(
      &mut ctx.program,
      &mut ctx.err_manager,
      &ctx.interner,
      config,
   );

   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }

   semantic_analysis::validator::validate_special_procedure_signatures(
      config.target,
      &mut ctx.interner,
      &ctx.program.procedure_name_table,
      &ctx.program.user_defined_types,
      &ctx.program.procedures,
      &mut ctx.err_manager,
   );

   let mut worklist: Vec<ProcedureId> = ctx
      .program
      .procedures
      .iter()
      .filter(|(_, v)| v.definition.type_parameters.is_empty() && v.impl_source == ProcImplSource::Native)
      .map(|(k, _)| k)
      .collect();
   let mut specializations: IndexMap<(ProcedureId, Box<[ExpressionType]>), ProcedureId> = IndexMap::new();
   let mut iteration: u64 = 0;

   let string_struct_id = {
      let UserDefinedTypeId::Struct(s_id) = ctx
         .program
         .user_defined_type_name_table
         .get(&ctx.interner.reverse_lookup("String").unwrap())
         .unwrap()
      else {
         unreachable!();
      };
      *s_id
   };

   let mut owned_validation_ctx = OwnedValidationContext {
      target: config.target,
      variable_types: IndexMap::new(),
      cur_procedure: None,
      loop_depth: 0,
      unknown_literals: IndexSet::new(),
      type_variables: TypeVariableManager::new(),
      cur_procedure_locals: IndexMap::new(),
      string_struct_id,
      procedures_to_specialize: Vec::new(),
   };

   semantic_analysis::validator::check_globals(
      &mut ctx.program,
      &mut owned_validation_ctx,
      &mut ctx.interner,
      &mut ctx.err_manager,
   );

   while !worklist.is_empty() {
      iteration += 1;
      if iteration == monomorphization::DEPTH_LIMIT {
         rolandc_error!(
            ctx.err_manager,
            ctx.program.procedures[worklist[0]].location,
            "Reached depth limit of {} during monomorphization",
            monomorphization::DEPTH_LIMIT
         );

         break;
      }

      for key in worklist.iter() {
         for parameter in ctx.program.procedures[*key].definition.parameters.iter_mut() {
            parameter.var_id = ctx.program.next_variable;
            ctx.program.next_variable = ctx.program.next_variable.next();
         }
      }

      let specs_to_create = semantic_analysis::validator::type_and_check_validity(
         &mut ctx.program,
         &mut ctx.err_manager,
         &mut ctx.interner,
         &mut owned_validation_ctx,
         &worklist,
      );
      worklist.clear();

      let specializations_before = specializations.len();
      monomorphization::monomorphize(&mut ctx.program, &mut specializations, specs_to_create);
      worklist.extend(specializations[specializations_before..].values());
   }
   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }
   semantic_analysis::type_inference::lower_type_variables(
      &mut owned_validation_ctx,
      &mut ctx.program.procedure_bodies,
      &mut ctx.program.ast.expressions,
      &mut ctx.err_manager,
   );
   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }
   ctx.program
      .procedures
      .retain(|_, x| x.definition.type_parameters.is_empty() || x.impl_source != ProcImplSource::Native);
   ctx.program
      .procedure_bodies
      .retain(|k, _| ctx.program.procedures.contains_key(k));
   // Throw out all untyped expressions, on the basis that untyped expressions should no
   // longer be referenced now that we deleted all template procedures
   ctx.program.ast.expressions.retain(|_, x| x.exp_type.is_some());

   loop_lowering::lower_fors_and_whiles(&mut ctx.program);

   defer::process_defer_statements(&mut ctx.program);

   definite_assignment::ensure_variables_definitely_assigned(&ctx.program, &mut ctx.err_manager);

   compile_consts::compile_consts(&mut ctx.program, &ctx.interner, &mut ctx.err_manager, config.target);

   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }

   logical_op_lowering::lower_logical_ops(&mut ctx.program);

   variable_declaration_lowering::lower_variable_decls(&mut ctx.program);

   if config.dump_debugging_info {
      pp::pp(
         &ctx.program,
         &ctx.interner,
         &mut std::fs::File::create("pp.rol").unwrap(),
      )
      .unwrap();
   }

   expression_hoisting::expression_hoisting(&mut ctx.program, &ctx.interner, HoistingMode::PreConstantFold);

   // must run after expression hoisting, so that re-ordering named arguments does not
   // affect side-effect order
   named_argument_lowering::lower_named_args(&mut ctx.program);

   constant_folding::fold_constants(&mut ctx.program, &mut ctx.err_manager, &ctx.interner, config.target);
   ctx.program
      .non_stack_var_info
      .retain(|_, v| v.kind != StorageKind::Const);

   if !ctx.err_manager.errors.is_empty() {
      return Err(CompilationError::Semantic);
   }

   Ok(())
}

pub struct CompilationConfig {
   pub target: Target,
   pub include_std: bool,
   pub i_am_std: bool,
   pub dump_debugging_info: bool,
}

pub fn compile<'a, FR: FileResolver<'a>>(
   ctx: &mut CompilationContext,
   user_program_ep: CompilationEntryPoint<'a, FR>,
   config: &CompilationConfig,
) -> Result<Vec<u8>, CompilationError> {
   compile_for_errors(ctx, user_program_ep, config)?;

   pre_backend_lowering::replace_nonnative_casts_and_unique_overflow(&mut ctx.program, &ctx.interner, config.target);

   if config.target == Target::Qbe {
      backend::qbe::replace_main_return_with_exit(&mut ctx.program, &ctx.interner);
   }

   dead_code_elimination::delete_unreachable_procedures_and_globals(&mut ctx.program, &mut ctx.interner, config.target);

   // (introduces usize types, so run this before those are lowered)
   expression_hoisting::expression_hoisting(&mut ctx.program, &ctx.interner, HoistingMode::AggregateLiteralLowering);

   pre_backend_lowering::lower_enums_and_pointers(&mut ctx.program, config.target);

   if config.target == Target::Qbe {
      expression_hoisting::expression_hoisting(&mut ctx.program, &ctx.interner, HoistingMode::ThreeAddressCode);
   }

   // Convert nested, AST representation into CFG
   {
      backend::linearize::linearize(
         &mut ctx.program,
         &ctx.interner,
         config.dump_debugging_info,
         config.target,
      );

      // Clean up
      for old_body in ctx.program.procedure_bodies.values_mut().map(|x| &mut x.block) {
         old_body.statements.clear();
      }
      ctx.program.ast.statements.clear();
   }

   // It would be nice to run this before deleting unreachable procedures,
   // but doing so would currently delete procedures that we take pointers to
   pre_backend_lowering::kill_zst_assignments(&mut ctx.program, config.target);

   if config.target != Target::Qbe {
      backend::wasm::sort_globals(&mut ctx.program, config.target);
   }

   let regalloc_result = {
      let mut program_liveness = SecondaryMap::with_capacity(ctx.program.procedure_bodies.len());
      for (id, body) in ctx.program.procedure_bodies.iter_mut() {
         let live_intervals = backend::liveness::compute_live_intervals(body, &ctx.program.ast.expressions);
         backend::liveness::kill_assignments_to_dead_variables(
            body,
            &live_intervals,
            &ctx.program.ast.expressions,
            &ctx.program.non_stack_var_info,
         );
         program_liveness.insert(id, live_intervals);
      }

      backend::regalloc::assign_variables_to_registers_and_mem(&ctx.program, config, &program_liveness)
   };

   backend::regalloc::kill_self_assignments(&mut ctx.program, &regalloc_result.var_to_slot);

   if config.target == Target::Qbe {
      Ok(backend::qbe::emit_qbe(&mut ctx.program, &ctx.interner, regalloc_result))
   } else {
      Ok(backend::wasm::emit_wasm(
         &mut ctx.program,
         &mut ctx.interner,
         config,
         regalloc_result,
      ))
   }
}

fn lex_and_parse(
   s: &str,
   source_path: SourcePath,
   err_manager: &mut ErrorManager,
   interner: &mut Interner,
   program: &mut Program,
) -> Result<Vec<ImportNode>, CompilationError> {
   let Ok(tokens) = lex::lex(s, source_path, err_manager, interner) else {
      return Err(CompilationError::Lex);
   };
   match parse::astify(tokens, err_manager, interner, program) {
      Err(()) => Err(CompilationError::Parse),
      Ok(imports) => Ok(imports),
   }
}
