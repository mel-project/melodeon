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
    let mut root_path = module_path.canonicalize()
     .map_err(|ctx| anyhow::anyhow!(format!("Failed to get absolute path for input file\n{}", ctx)))?;
    if root_path.is_file() { root_path.pop(); }

    let mut demod = Demodularizer::new_at_fs(&root_path, &root_path.join("melo-libs"));
    let modid = context::ProjectRoot(root_path.clone()).module_from_root(Path::new("."));
    demod.module_override(modid, melo_code.to_string());

    let raw = demod.demod(modid, &root_path)?;
    let prgrm = typesys::typecheck_program(raw)?;
    Ok(codegen::codegen_program(prgrm))
}
