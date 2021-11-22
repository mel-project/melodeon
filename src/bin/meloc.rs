#![recursion_limit = "256"]

use std::{path::Path, time::Instant};

use argh::FromArgs;
use log::LevelFilter;
use melodeon_rs::{
    codegen::codegen_program,
    context::{Ctx, CtxResult, ModuleId, ToCtxErr},
    demod::Demodularizer,
    grammar::{parse_program, RawProgram},
    typesys::typecheck_program,
};

#[derive(FromArgs)]
/// Low-level melodeon compiler
struct Args {
    #[argh(option)]
    /// input file
    input: String,
}

fn main() {
    let args: Args = argh::from_env();
    init_logs();
    main_inner(args).unwrap();
}

fn main_inner(args: Args) -> CtxResult<()> {
    let loader = Demodularizer::new_at_fs(Path::new("."));
    let raw_input = time_stage("parse+demod", || {
        loader.demod(ModuleId::from_path(Path::new(&args.input)))
    })?;
    let tchecked = time_stage("typecheck", || typecheck_program(raw_input))?;
    let product = time_stage("codegen", || codegen_program(tchecked));
    println!("{}", product);
    Ok(())
}

fn time_stage<T>(label: &str, action: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let res = action();
    log::info!("[{}] took {:?}", label, start.elapsed());
    res
}

fn preload_module(mid: ModuleId) -> CtxResult<Ctx<RawProgram>> {
    log::info!("loading module {:?}", mid);
    let ss = mid.load_file().err_ctx(None)?;
    let parsed = parse_program(&ss, mid)?;
    Ok(parsed)
}

fn init_logs() {
    let _ = env_logger::builder()
        .format_timestamp(None)
        .filter_level(LevelFilter::Debug)
        .try_init();
}
