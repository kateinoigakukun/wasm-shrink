use std::{collections::HashMap, hash::Hash, path::PathBuf};
use structopt::StructOpt;
use walrus::ir::{Visitor, VisitorMut};

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
    merge_funcs(&mut module);
    module.emit_wasm_file(opt.output)?;
    Ok(())
}

struct HashInstr(String);

impl HashInstr {
    fn new(instr: &walrus::ir::Instr) -> Self {
        Self(format!("{:?}", instr))
    }
}

impl Hash for HashInstr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write(self.0.as_bytes());
    }
}

impl PartialEq for HashInstr {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for HashInstr {}

#[derive(PartialEq, Eq, Hash)]
struct FunctionKey(Vec<HashInstr>, walrus::TypeId);

fn compute_func_key(func: &walrus::LocalFunction) -> FunctionKey {
    struct InstCollector {
        instrs: Vec<HashInstr>,
    }

    impl<'a> Visitor<'a> for InstCollector {
        fn visit_instr(&mut self, instr: &'a walrus::ir::Instr, _: &'a walrus::InstrLocId) {
            self.instrs.push(HashInstr::new(instr));
        }
    }

    let mut collector = InstCollector { instrs: Vec::new() };
    let entry = func.entry_block();
    walrus::ir::dfs_in_order(&mut collector, func, entry);
    FunctionKey(collector.instrs, func.ty())
}

fn merge_funcs(module: &mut walrus::Module) {
    let mut func_hashmap = HashMap::new();
    let mut replacing_map = HashMap::new();

    for (id, func) in module.funcs.iter_local() {
        let key = compute_func_key(func);
        if let Some(existing) = func_hashmap.get(&key) {
            let (existing, _) = existing;
            replacing_map.insert(id, *existing);
        } else {
            func_hashmap.insert(key, (id, func));
        }
    }

    struct Replacer<'a> {
        replacing_map: &'a HashMap<walrus::FunctionId, walrus::FunctionId>,
    }

    impl VisitorMut for Replacer<'_> {
        fn visit_call_mut(&mut self, instr: &mut walrus::ir::Call) {
            if let Some(replacing_id) = self.replacing_map.get(&instr.func) {
                instr.func = *replacing_id;
            }
        }
    }

    for (_, func) in module.funcs.iter_local_mut() {
        let entry = func.entry_block();
        walrus::ir::dfs_pre_order_mut(
            &mut Replacer {
                replacing_map: &replacing_map,
            },
            func,
            entry,
        );
    }

    for (from, _) in replacing_map.iter() {
        module.funcs.delete(*from);
    }

    for element in module.elements.iter_mut() {
        for (i, member) in element.members.clone().iter().enumerate() {
            let member = match member {
                Some(member) => member,
                None => continue,
            };
            let to_func_id = match replacing_map.get(member) {
                Some(func_id) => func_id,
                None => continue,
            };
            element.members[i] = Some(*to_func_id);
        }
    }
}
