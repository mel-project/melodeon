#![recursion_limit = "256"]

use std::{path::Path, time::Instant};

use argh::FromArgs;

use log::LevelFilter;
use melodeon::{
    codegen::codegen_program,
    context::{CtxResult, ModuleId},
    demod::Demodularizer,
    typesys::typecheck_program,
};
use tracing::Level;
use tracing_subscriber::FmtSubscriber;

#[derive(FromArgs)]
/// Low-level melodeon compiler
struct Args {
    #[argh(positional)]
    /// input file
    input: String,
    #[argh(option, default = "\"output.mil\".to_string()")]
    /// input file
    output: String,
    #[argh(option, default = "\"./.melo-libs\".to_string()")]
    /// library directory
    lib_dir: String,
    #[argh(option, default = "false")]
    /// silence all log messages
    no_logs: bool,
}

fn main() {
    // a builder for `FmtSubscriber`.
    let subscriber = FmtSubscriber::builder()
        // all spans/events with a level higher than TRACE (e.g, debug, info, warn, etc.)
        // will be written to stdout.
        .with_max_level(Level::DEBUG)
        .with_writer(std::io::stderr)
        // completes the builder.
        .finish();
    tracing::subscriber::set_global_default(subscriber).expect("setting default subscriber failed");
    let args: Args = argh::from_env();

    let loader = Demodularizer::new_at_fs(Path::new("."), Path::new(&args.lib_dir));
    if let Err(err) = main_inner(args, &loader) {
        eprintln!("{}", err);

        std::process::exit(255);
    }
}

fn main_inner(args: Args, loader: &Demodularizer) -> CtxResult<()> {
    let raw_input = time_stage("parse+demod", || {
        let mut root = std::path::PathBuf::from(args.input.clone());
        root.pop();
        loader.demod(ModuleId::from_path(Path::new(&args.input)), &root)
    })?;
    let tchecked = time_stage("typecheck", || typecheck_program(raw_input))?;
    let product = time_stage("codegen", || codegen_program(tchecked).enclose().unwrap());
    println!(
        "{}",
        serde_yaml::to_string(&serde_json::to_value(&product).unwrap()).unwrap()
    );
    println!("{:?}", product.eval());
    let compiled = mil2::assemble(&mil2::compile_mil(product)?)?;
    let result = melvm::Covenant::from_ops(&compiled)
        .debug_execute(&[], 100000)
        .unwrap();
    println!("{:?}", result);
    Ok(())
}

fn time_stage<T>(label: &str, action: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let res = action();
    log::info!("[{}] took {:?}", label, start.elapsed());
    res
}

fn init_logs() {
    let _ = env_logger::builder()
        .format_timestamp(None)
        .filter_level(LevelFilter::Debug)
        .try_init();
}
