use walrus::LocalFunction;

pub mod merge;

#[derive(Debug, Clone, Copy)]
pub struct WasmFeatures {
    pub reference_types: bool,
}

impl WasmFeatures {
    pub fn detect_from(module: &walrus::Module) -> Self {
        let mut this = Self {
            reference_types: false,
        };
        for func in module.functions() {
            match &func.kind {
                walrus::FunctionKind::Import(_) => continue,
                walrus::FunctionKind::Uninitialized(_) => continue,
                walrus::FunctionKind::Local(local_fn) => this.detect_from_function(local_fn),
            }
        }
        this
    }

    fn detect_from_function<'a>(&'a mut self, func: &LocalFunction) {
        struct Visitor<'a> {
            this: &'a mut WasmFeatures,
        }
        impl<'instr> walrus::ir::Visitor<'instr> for Visitor<'_> {
            fn visit_instr(
                &mut self,
                instr: &'instr walrus::ir::Instr,
                _: &'instr walrus::InstrLocId,
            ) {
                use walrus::ir::Instr;
                match instr {
                    Instr::TableCopy(_)
                    | Instr::TableFill(_)
                    | Instr::TableGet(_)
                    | Instr::TableSet(_)
                    | Instr::TableInit(_)
                    | Instr::ElemDrop(_)
                    | Instr::RefNull(_)
                    | Instr::RefFunc(_)
                    | Instr::RefIsNull(_) => {
                        self.this.reference_types = true;
                    }
                    _ => {}
                }
            }
        }
        walrus::ir::dfs_in_order(&mut Visitor { this: self }, func, func.entry_block())
    }
}
