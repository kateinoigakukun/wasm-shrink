use anyhow::anyhow;
use std::path::PathBuf;
use structopt::StructOpt;
mod merge;

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
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let module_config = walrus::ModuleConfig::new();
    let mut module = module_config.parse_file(opt.file)?;
    match opt.merge_strategy.as_str() {
        "exact-match" => merge::exact_match::merge_funcs(&mut module),
        "const-param" => merge::const_param::merge_funcs(&mut module),
        other => return Err(anyhow!("Unknown merge strategy {}", other)),
    }

    module.emit_wasm_file(opt.output)?;
    Ok(())
}
