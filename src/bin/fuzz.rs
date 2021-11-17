use melodeon_rs::{
    codegen::codegen_program,
    containers::Symbol,
    context::{CtxResult, ModuleId},
    grammar::parse_program,
    typesys::typecheck_program,
};

#[cfg(fuzzing)]
fn main() {
    use log::LevelFilter;
    let _ = env_logger::builder()
        .filter_level(LevelFilter::Trace)
        .try_init();
    loop {
        honggfuzz::fuzz!(|data: &[u8]| {
            test_once(&data);
        });
    }
}

fn test_once(data: &[u8]) -> CtxResult<()> {
    let module = ModuleId(Symbol::from("whatever.melo"));
    let data = String::from_utf8_lossy(data);
    log::info!("input string: {:?}", data);
    let res = codegen_program(typecheck_program(parse_program(&data, module)?)?);
    log::info!("compiled output: {}", res);
    Ok(())
}

#[cfg(not(fuzzing))]
fn main() {}
