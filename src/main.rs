use anyhow::anyhow;
use std::path::PathBuf;
use structopt::StructOpt;
use wasm_shrink::{merge, WasmFeatures};

#[derive(StructOpt, Debug)]
struct Opt {
    /// .wasm file to process
    #[structopt(name = "FILE")]
    file: PathBuf,

    /// output file path
    #[structopt(short, long)]
    output: PathBuf,

    #[structopt(default_value = "exact-match", long)]
    merge_strategy: String,

    #[structopt(long)]
    enable_reference_types: bool,

    #[structopt(long)]
    stats: Option<PathBuf>,
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let mut module_config = walrus::ModuleConfig::new();
    module_config.strict_validate(false);
    let mut module = module_config.parse_file(opt.file)?;
    let mut features = WasmFeatures::detect_from(&module);

    if opt.enable_reference_types {
        features.reference_types = true;
    }

    match opt.merge_strategy.as_str() {
        "exact-match" => merge::exact_match::merge_funcs(&mut module),
        "const-param" => {
            let stats = merge::const_param::merge_funcs(&mut module, features);
            if let Some(stats_path) = opt.stats {
                write_stats(stats_path, &stats)
            }
        }
        other => return Err(anyhow!("Unknown merge strategy {}", other)),
    }

    module.emit_wasm_file(opt.output)?;
    Ok(())
}

fn write_stats<S: serde::Serialize>(stats_path: PathBuf, stats: &S) {
    let stats_file = match std::fs::File::create(stats_path) {
        Ok(stats_file) => stats_file,
        Err(e) => {
            log::warn!("failed to create stats file: {}", e);
            return;
        }
    };
    match serde_json::to_writer_pretty(stats_file, stats) {
        Ok(()) => (),
        Err(e) => {
            log::warn!("failed to write to stats file: {}", e);
            return;
        }
    };
}
