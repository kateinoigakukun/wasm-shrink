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
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();

    let module_config = walrus::ModuleConfig::new();
    let mut module = module_config.parse_file(opt.file)?;
    merge::exact_match::merge_funcs(&mut module);
    module.emit_wasm_file(opt.output)?;
    Ok(())
}
