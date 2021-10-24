use std::collections::{HashMap, HashSet};
use walrus::{ElementId, ExportId, FunctionId};

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum FunctionUse {
    Call { caller: FunctionId },
    InElement { element: ElementId, index: usize },
    Export { export: ExportId },
}

#[derive(Debug, Default)]
pub struct CallGraph {
    // FIXME: Think more efficient data structure
    callee_to_uses: HashMap<FunctionId, HashSet<FunctionUse>>,
}

impl CallGraph {
    pub fn build_from(module: &walrus::Module) -> Self {
        let mut graph = CallGraph::default();

        // Collect direct calls
        for (func_id, func) in module.funcs.iter_local() {
            let mut collector = CallCollector {
                graph: &mut graph,
                func_id,
            };
            walrus::ir::dfs_in_order(&mut collector, func, func.entry_block());
        }

        // Collect indirect function table elements
        for element in module.elements.iter() {
            for (index, member) in element.members.clone().iter().enumerate() {
                if let Some(member) = member {
                    graph.add_use(
                        *member,
                        FunctionUse::InElement {
                            element: element.id(),
                            index,
                        },
                    );
                }
            }
        }

        // Collect exports having references to functions
        for export in module.exports.iter() {
            match export.item {
                walrus::ExportItem::Function(func) => graph.add_use(
                    func,
                    FunctionUse::Export {
                        export: export.id(),
                    },
                ),
                _ => (),
            }
        }

        graph
    }

    pub fn get_func_uses(&self, func_id: &FunctionId) -> Option<&HashSet<FunctionUse>> {
        self.callee_to_uses.get(func_id)
    }

    pub fn add_function(&mut self, id: FunctionId, local_func: &walrus::LocalFunction) {
        let mut collector = CallCollector {
            graph: self,
            func_id: id,
        };
        walrus::ir::dfs_in_order(&mut collector, local_func, local_func.entry_block());
    }

    /// delete a given function from graph assuming uses of the function have been removed
    pub fn delete_function_unsafe(&mut self, id: &FunctionId, local_func: &walrus::LocalFunction) {
        self.callee_to_uses.remove(id);

        let mut deleter = CallDeleter {
            func_id: *id,
            graph: self,
        };
        walrus::ir::dfs_in_order(&mut deleter, local_func, local_func.entry_block());
    }

    fn add_use(&mut self, callee: FunctionId, use_entry: FunctionUse) {
        self.callee_to_uses
            .entry(callee)
            .or_default()
            .insert(use_entry);
    }

    fn delete_use(&mut self, callee: FunctionId, use_entry: &FunctionUse) {
        if let Some(uses) = self.callee_to_uses.get_mut(&callee) {
            uses.remove(use_entry);
        }
    }
}

struct CallCollector<'graph> {
    func_id: FunctionId,
    graph: &'graph mut CallGraph,
}

impl<'instr> walrus::ir::Visitor<'instr> for CallCollector<'_> {
    fn visit_call(&mut self, instr: &walrus::ir::Call) {
        self.graph.add_use(
            instr.func,
            FunctionUse::Call {
                caller: self.func_id,
            },
        );
    }
}

struct CallDeleter<'graph> {
    func_id: FunctionId,
    graph: &'graph mut CallGraph,
}

impl<'instr> walrus::ir::Visitor<'instr> for CallDeleter<'_> {
    fn visit_call(&mut self, instr: &walrus::ir::Call) {
        self.graph.delete_use(
            instr.func,
            &FunctionUse::Call {
                caller: self.func_id,
            },
        );
    }
}
