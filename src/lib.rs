pub mod codegen;
pub mod containers;
pub mod context;
pub mod demod;
pub mod grammar;
pub mod typed_ast;
pub mod typesys;

use std::path::Path;

use demod::Demodularizer;
use typesys::Type;

/// Compiles a melodeon program by its literal string, resolving dependencies assuming that the string was read from a file at the given module path. Returns the Mil representation, as well as the type of the
pub fn compile(melo_code: &str, module_path: &Path) -> context::CtxResult<(String, Type)> {
    let mut root_path = module_path
        .canonicalize()
        .unwrap_or_else(|_| module_path.to_owned());
    if root_path.is_file() {
        root_path.pop();
    }
    let fname = module_path.file_name();

    let mut demod = Demodularizer::new_at_fs(&root_path, &root_path.join("melo-libs"));
    let modid = if let Some(f) = fname {
        context::ProjectRoot(root_path.clone()).module_from_root(f.as_ref())
    } else {
        context::ProjectRoot(root_path.clone()).module_from_root(Path::new("."))
    };
    demod.module_override(modid, melo_code.to_string());

    let raw = demod.demod(modid, &root_path)?;
    let prgrm = typesys::typecheck_program(raw)?;
    let t = prgrm.body.itype.clone();
    Ok((codegen::codegen_program(prgrm), t))
}
