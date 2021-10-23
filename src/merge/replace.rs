use std::collections::HashMap;

use walrus::{ExportItem, ir::VisitorMut};

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
) {
    for (_, func) in module.funcs.iter_local_mut() {
        let entry = func.entry_block();
        walrus::ir::dfs_pre_order_mut(&mut Replacer { replacing_map: map }, func, entry);
    }

    for element in module.elements.iter_mut() {
        for (i, member) in element.members.clone().iter().enumerate() {
            let member = match member {
                Some(member) => member,
                None => continue,
            };
            let to_func_id = match map.get(member) {
                Some(func_id) => func_id,
                None => continue,
            };
            element.members[i] = Some(*to_func_id);
        }
    }

    for export in module.exports.iter_mut() {
        let item = match export.item {
            ExportItem::Function(from) => {
                if let Some(to) = map.get(&from) {
                    ExportItem::Function(*to)
                } else {
                    ExportItem::Function(from)
                }
            }
            other => other,
        };
        export.item = item;
    }

    for (from, _) in map.iter() {
        module.funcs.delete(*from);
    }
}
