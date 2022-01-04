pub mod codegen;
pub mod containers;
pub mod context;
pub mod demod;
pub mod grammar;
pub mod typed_ast;
pub mod typesys;

use std::path::Path;

pub fn compile(melo_code: &str, module_path: &Path) -> context::CtxResult<String> {
    let raw = grammar::parse_program(melo_code, context::ModuleId::from_path(module_path))?;
    let prgrm = typesys::typecheck_program(raw)?;
    Ok(codegen::codegen_program(prgrm))
}
