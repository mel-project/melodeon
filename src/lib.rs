pub mod codegen;
pub mod containers;
pub mod context;
pub mod demod;
pub mod grammar;
pub mod typed_ast;
pub mod typesys;

use std::path::Path;

use demod::Demodularizer;

/// Compiles a melodeon program by its literal string, resolving dependencies assuming that the string was read from a file at the given module path.
pub fn compile(melo_code: &str, module_path: &Path) -> context::CtxResult<String> {
    let mut demod = Demodularizer::new_at_fs(module_path, Path::new("./.melo-libs/"));
    let modid = context::ModuleId::from_path(module_path);
    demod.module_override(modid, melo_code.to_string());
    let raw = demod.demod(modid)?;
    let prgrm = typesys::typecheck_program(raw)?;
    Ok(codegen::codegen_program(prgrm))
}
