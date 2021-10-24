use std::collections::{HashMap, HashSet};
use walrus::{ir::VisitorMut, ExportItem};
use crate::merge::call_graph::{CallGraph, FunctionUse};

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

pub fn replace_funcs(
    map: &HashMap<walrus::FunctionId, walrus::FunctionId>,
    module: &mut walrus::Module,
    call_graph: &mut CallGraph,
) {
    let mut func_worklist = HashSet::new();

    for (from, to) in map.iter() {
        let uses = match call_graph.get_func_uses(from) {
            Some(uses) => uses,
            None => continue,
        };

        for func_use in uses {
            match func_use {
                FunctionUse::Call { caller } => {
                    func_worklist.insert(caller);
                }
                FunctionUse::InElement { element, index } => {
                    let element = module.elements.get_mut(*element);
                    element.members[*index] = Some(*to);
                }
                FunctionUse::Export { export } => {
                    let export = module.exports.get_mut(*export);
                    if let ExportItem::Function(func) = &mut export.item {
                        *func = *to;
                    } else {
                        unreachable!("unexpected non-function export name={}", export.name);
                    }
                }
            }
        }
    }

    for func in func_worklist {
        let func = module.funcs.get_mut(*func).kind.unwrap_local_mut();
        let entry = func.entry_block();
        walrus::ir::dfs_pre_order_mut(&mut Replacer { replacing_map: map }, func, entry);
    }

    for (from, _) in map.iter() {
        let func = module.funcs.get_mut(*from).kind.unwrap_local_mut();
        call_graph.delete_function_unsafe(from, &func);
        module.funcs.delete(*from);
    }
}
