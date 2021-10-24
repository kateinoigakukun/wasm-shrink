use std::{collections::HashMap, hash::Hash};
use walrus::ir::{Visitor, VisitorMut};

use crate::merge::replace;

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

pub fn merge_funcs(module: &mut walrus::Module) {
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

    let mergable_funcs = replacing_map.len();
    log::debug!("mergable_funcs = {}", mergable_funcs);

    replace::replace_funcs(&replacing_map, module);
}
