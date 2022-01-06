#![recursion_limit = "256"]

use std::{path::Path, time::Instant};

use argh::FromArgs;
use colored::Colorize;
use log::LevelFilter;
use melodeon::{
    codegen::codegen_program,
    context::{CtxResult, ModuleId, ToCtxErr},
    demod::Demodularizer,
    typesys::typecheck_program,
};

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
    let args: Args = argh::from_env();
    if !args.no_logs {
        init_logs();
    }
    let loader = Demodularizer::new_at_fs(Path::new("."), Path::new(&args.lib_dir));
    if let Err(err) = main_inner(args, &loader) {
        eprintln!("{}", err);
        /*
        let error_location: String;
        let mut detailed_line: Option<String> = None;
        if let Some(ctx) = err.ctx() {
            if let Ok(source_full_string) =
                std::fs::read_to_string(Path::new(&ctx.source.to_string()))
            {
                let mut char_counter = 0;
                let mut errloc = ctx.source.to_string();
                for (lineno, line) in source_full_string.split('\n').enumerate() {
                    let line_len = line.len() + 1;
                    if char_counter + line.len() > ctx.start_offset {
                        let line_offset = ctx.start_offset - char_counter;
                        errloc = format!("{}:{}", ctx.source, lineno + 1);
                        detailed_line = Some(format!("{}\n{}", line, {
                            let mut toret = String::new();
                            for _ in 0..line_offset {
                                toret.push(' ');
                            }
                            toret.push_str(&format!("{}", "^".bright_green().bold()));
                            for _ in
                                1..(ctx.end_offset - ctx.start_offset).min(line.len() - line_offset)
                            {
                                toret.push_str(&format!("{}", "~".bright_green().bold()));
                            }
                            toret
                        }));
                        break;
                    }
                    char_counter += line_len
                }
                error_location = errloc;
            } else {
                error_location = ctx.source.to_string();
            }
        } else {
            error_location = "(unknown location)".to_string();
        }
        eprintln!(
            "{}: {} {}",
            error_location.bold(),
            "error:".bold().red(),
            err.to_string().bold()
        );
        if let Some(line) = detailed_line {
            for line in line.lines() {
                eprintln!("\t{}", line);
            }
        }
        */
        std::process::exit(255);
    }
}

fn main_inner(args: Args, loader: &Demodularizer) -> CtxResult<()> {
    let raw_input = time_stage("parse+demod", || {
        loader.demod(ModuleId::from_path(Path::new(&args.input)))
    })?;
    let tchecked = time_stage("typecheck", || typecheck_program(raw_input))?;
    let product = time_stage("codegen", || codegen_program(tchecked));
    std::fs::write(Path::new(args.output.as_str()), product.as_bytes()).err_ctx(None)?;
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
