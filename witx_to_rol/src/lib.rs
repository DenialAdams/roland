use std::{fmt::Write, result};
use std::ops::Deref;
use std::path::Path;

use witx::{TypeRef, WitxError};

struct Ctx {
   indentation_level: usize,
   output: String,
}

impl Ctx {
   fn indent(&mut self) {
      for _ in 0..self.indentation_level {
         self.output.push_str("   ");
      }
   }
}

pub fn witx_to_rol<P: AsRef<Path>>(input: P) -> Result<String, WitxError> {
   let mut ctx = Ctx {
      indentation_level: 0,
      output: String::new(),
   };

   let document = witx::load(&[input])?;

   for named_types in document.typenames() {
      emit_type(named_types.name.as_str(), &named_types.tref, &mut ctx);
      ctx.output.push('\n');
   }

   for _constant in document.constants() {
      unimplemented!();
   }

   for module in document.modules() {
      for func in module.funcs() {
         write!(ctx.output, "extern proc __wasi_{}(", func.name.as_str()).unwrap();
         for param in func.params.iter() {
            write!(ctx.output, "{}: ", param.name.as_str()).unwrap();
            emit_type("", &param.tref, &mut ctx);
            ctx.output.push_str(", ");
         }
         if !func.params.is_empty() {
            let _ = ctx.output.pop();
            let _ = ctx.output.pop();
         }
         ctx.output.push(')');
         if func.noreturn {
            ctx.output.push_str(" -> !");
         } else if !func.results.is_empty() {
            ctx.output.push_str("-> ");
         }
         if func.results.len() > 1 {
            unimplemented!();
         }
         for result in &func.results {
            emit_type("", &result.tref, &mut ctx);
         }
         ctx.output.push('\n');
      }
   }

   println!("{}", &ctx.output);

   todo!()
}

fn emit_type(name: &str, e_type: &TypeRef, ctx: &mut Ctx) {
   match e_type {
      TypeRef::Name(inner) => {
         write!(ctx.output, "__wasi_{}", inner.name.as_str()).unwrap();
      }
      TypeRef::Value(the_type) => {
         match the_type.deref() {
            witx::Type::Record(record_details) => {
               if let Some(int_repr) = record_details.bitflags_repr() {
                  ctx.output.push_str("// skipping flags ");
                  ctx.output.push_str(name);
                  let str = match int_repr {
                     witx::IntRepr::U8 => "u8",
                     witx::IntRepr::U16 => "u16",
                     witx::IntRepr::U32 => "u32",
                     witx::IntRepr::U64 => "u64",
                  };
                  ctx.output.push_str(str);
               } else {
                  writeln!(ctx.output, "struct __wasi_{} {{", name).unwrap();
                  ctx.indentation_level += 1;
                  for member in record_details.members.iter() {
                     ctx.indent();
                     write!(ctx.output, "{}: ", member.name.as_str()).unwrap();
                     emit_type("", &member.tref, ctx);
                     ctx.output.push_str("\n");
                  }
                  ctx.indentation_level -= 1;
                  ctx.output.push_str("}");
               }
            }
            witx::Type::Variant(_) => {
               write!(ctx.output, "// skipping variant type {}", name).unwrap();
            }
            witx::Type::Handle(_) => {
               write!(ctx.output, "// skipping handle type {}", name).unwrap();
            }
            witx::Type::List(_) => {
               write!(ctx.output, "// skipping list type {}", name).unwrap();
            }
            witx::Type::Pointer(inner) |  witx::Type::ConstPointer(inner) => {
               ctx.output.push('&');
               emit_type("", inner, ctx);
            },
            witx::Type::Builtin(bt) => {
               if name != "" {
                  write!(ctx.output, "// skipping type alias {}", name).unwrap();
                  return;
               }
               let str = match bt {
                  witx::BuiltinType::Char => "u32 // char",
                  witx::BuiltinType::U8 { lang_c_char: _ } => "u8",
                  witx::BuiltinType::U16 => "u16",
                  witx::BuiltinType::U32 { lang_ptr_size } => {
                     if *lang_ptr_size {
                        "usize"
                     } else {
                        "u32"
                     }
                  }
                  witx::BuiltinType::U64 => "u64",
                  witx::BuiltinType::S8 => "i8",
                  witx::BuiltinType::S16 => "i16",
                  witx::BuiltinType::S32 => "i32",
                  witx::BuiltinType::S64 => "i64",
                  witx::BuiltinType::F32 => "f32",
                  witx::BuiltinType::F64 => "f64",
               };
               ctx.output.push_str(str);
            }
         }
      }
   }
}

#[cfg(test)]
mod tests {
   use crate::witx_to_rol;

   #[test]
   fn wasi_witx() {
      witx_to_rol("wasi_snapshot_preview1.witx").unwrap();
   }
}
