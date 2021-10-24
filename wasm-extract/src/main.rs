use std::{collections::HashSet, ops::Sub, path::PathBuf};

use anyhow::{anyhow, Context};
use structopt::StructOpt;
use walrus::{
    ir::Visitor, Element, ElementKind, Export, ExportItem, Function, FunctionId, Import, ImportId,
    ImportKind, Table, TableId,
};

#[derive(StructOpt, Debug)]
struct Opt {
    #[structopt(name = "FILE")]
    input: PathBuf,

    #[structopt(short, long)]
    output: PathBuf,

    /// Specify function to extract
    #[structopt(name = "func", short, long)]
    funcs: Vec<String>,
}

#[derive(Debug)]
struct Retainer<'module> {
    module: &'module walrus::Module,
    imports: HashSet<ImportId>,
    funcs: HashSet<FunctionId>,
    tables: HashSet<TableId>,
}

impl<'instr> Visitor<'instr> for Retainer<'_> {
    fn visit_function_id(&mut self, function: &walrus::FunctionId) {
        self.retain_func(*function, self.module)
    }

    fn visit_table_id(&mut self, table: &walrus::TableId) {
        self.tables.insert(*table);
    }
}

impl<'module> Retainer<'module> {
    fn new(module: &'module walrus::Module) -> Self {
        Self {
            module,
            imports: HashSet::new(),
            funcs: HashSet::new(),
            tables: HashSet::new(),
        }
    }

    fn retain_func(&mut self, func: FunctionId, module: &walrus::Module) {
        if self.funcs.contains(&func) {
            return;
        }

        self.funcs.insert(func);
        let func = module.funcs.get(func);
        match &func.kind {
            walrus::FunctionKind::Import(import) => {
                self.imports.insert(import.import);
            }
            walrus::FunctionKind::Local(local) => {
                walrus::ir::dfs_in_order(self, local, local.entry_block());
            }
            walrus::FunctionKind::Uninitialized(_) => unreachable!(),
        }
    }
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();
    let mut module = walrus::Module::from_file(opt.input)?;

    let mut keeping_funcs = vec![];

    for func in opt.funcs {
        let func_id = module
            .funcs
            .by_name(&func)
            .with_context(|| anyhow!("function not found '{}'", func))?;
        keeping_funcs.push((func, func_id));
    }

    let (removing_funcs, removing_tables, removing_exports, removing_imports, removing_elements) = {
        let mut retainer = Retainer::new(&module);

        for (_, func) in keeping_funcs.iter() {
            retainer.retain_func(*func, &module)
        }

        let all_funcs = module
            .funcs
            .iter()
            .map(Function::id)
            .collect::<HashSet<_>>();
        let all_tables = module.tables.iter().map(Table::id).collect::<HashSet<_>>();
        let all_exports = module
            .exports
            .iter()
            .map(Export::id)
            .collect::<HashSet<_>>();

        let removing_funcs = all_funcs.sub(&retainer.funcs);
        let removing_tables = all_tables.sub(&retainer.tables);
        let removing_imports = module
            .imports
            .iter()
            .filter(|import| match import.kind {
                ImportKind::Function(func) => removing_funcs.contains(&func),
                _ => false,
            })
            .map(Import::id)
            .collect::<HashSet<_>>();

        let removing_elements = module
            .elements
            .iter()
            .filter(|elem| match elem.kind {
                ElementKind::Active { table, .. } => removing_tables.contains(&table),
                _ => false,
            })
            .map(Element::id)
            .collect::<HashSet<_>>();

        (
            removing_funcs,
            removing_tables,
            all_exports,
            removing_imports,
            removing_elements,
        )
    };

    for export in removing_exports {
        module.exports.delete(export);
    }

    for import in removing_imports {
        module.imports.delete(import);
    }

    for func in removing_funcs {
        module.funcs.delete(func);
    }

    for table in removing_tables {
        module.tables.delete(table);
    }

    for elem in removing_elements {
        module.elements.delete(elem);
    }

    let tmp_keepings = keeping_funcs
        .iter()
        .map(|(func, id)| module.exports.add(func, ExportItem::Function(*id)))
        .collect::<Vec<_>>();

    walrus::passes::gc::run(&mut module);

    for keeping in tmp_keepings {
        module.exports.delete(keeping);
    }

    module.emit_wasm_file(opt.output)?;
    Ok(())
}
