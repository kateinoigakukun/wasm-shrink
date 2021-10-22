//! Constant Parameterization


use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use walrus::ir::{
    Br, BrIf, GlobalGet, GlobalSet, IfElse, Instr, InstrSeqId, LocalGet, LocalSet,
    LocalTee, MemoryGrow, MemorySize, TableFill, TableGet, TableGrow, TableSet, TableSize, Value,
};
use walrus::{InstrLocId, LocalFunction, LocalId};

use super::func_hash;

#[derive(PartialEq, Eq, Debug, Hash)]
struct FunctionHash(u64);

impl FunctionHash {
    fn hash(f: &walrus::Function, module: &walrus::Module) -> Option<Self> {
        let f = match f.kind {
            walrus::FunctionKind::Import(_) => return None,
            walrus::FunctionKind::Local(ref f) => f,
            walrus::FunctionKind::Uninitialized(_) => return None,
        };
        Some(FunctionHash::hash_local(f, module))
    }
    fn hash_local(f: &walrus::LocalFunction, module: &walrus::Module) -> Self {
        let mut hasher = DefaultHasher::new();
        let ty = module.types.get(f.ty());
        ty.hash(&mut hasher);
        func_hash::run(f, &mut hasher);
        Self(hasher.finish())
    }
}

pub fn merge_funcs(module: &mut walrus::Module) {
    let mut hashed_group: HashMap<FunctionHash, Vec<&walrus::Function>> = HashMap::new();
    for f in module.funcs.iter() {
        let key = match FunctionHash::hash(f, &module) {
            Some(key) => key,
            None => continue,
        };
        if let Some(group) = hashed_group.get_mut(&key) {
            group.push(f)
        } else {
            hashed_group.insert(key, vec![f]);
        }
    }

    let mut deferred = vec![];
    log::debug!("Dump functions grouped by hash");
    for (key, group) in hashed_group {
        if group.len() < 2 {
            continue;
        }
        log::debug!("Group #{}", key.0);
        for f in group {
            deferred.push(f);
            log::debug!(" - {:?}", f.name);
        }
    }
}

struct IdPairMap<Id: Hash + Eq> {
    lhs_to_rhs: HashMap<Id, Id>,
}

impl<Id: Hash + Eq> Deref for IdPairMap<Id> {
    type Target = HashMap<Id, Id>;
    fn deref(&self) -> &Self::Target {
        &self.lhs_to_rhs
    }
}

impl<Id: Hash + Eq> IdPairMap<Id> {
    fn new() -> Self {
        Self {
            lhs_to_rhs: HashMap::new(),
        }
    }

    /// Returns `true` iff the pair of local id is not compatible with former uses
    fn record(&mut self, lhs: Id, rhs: Id) -> bool {
        match self.lhs_to_rhs.get(&lhs) {
            Some(found_rhs) => found_rhs != &rhs,
            None => {
                self.lhs_to_rhs.insert(lhs, rhs);
                false
            }
        }
    }
}

#[allow(unused)]
fn are_in_equivalence_class(lhs: &walrus::Function, rhs: &walrus::Function, module: &walrus::Module) -> bool {
    let (lhs, rhs) = match (&lhs.kind, &rhs.kind) {
        (walrus::FunctionKind::Local(lhs), walrus::FunctionKind::Local(rhs)) => (lhs, rhs),
        _ => return false,
    };
    if lhs.ty() != rhs.ty() {
        return false;
    }

    let lhs_iter = dfs_pre_order_iter(&lhs, lhs.entry_block());
    let rhs_iter = dfs_pre_order_iter(&rhs, rhs.entry_block());

    let mut locals_map = IdPairMap::<LocalId>::new();
    let mut seqs_map = IdPairMap::<InstrSeqId>::new();

    for (lhs_instr, rhs_instr) in lhs_iter.zip(rhs_iter) {
        if lhs_instr.opcode() != rhs_instr.opcode() {
            return false;
        }
        match (lhs_instr, rhs_instr) {
            (Instr::Block(_), Instr::Block(_)) => {}
            (Instr::Loop(_), Instr::Loop(_)) => {}
            (Instr::Call(lhs_call), Instr::Call(rhs_call)) => {
                // TODO: merge different callee
                if lhs_call.func != rhs_call.func {
                    return false;
                }
            }
            (Instr::CallIndirect(lhs_call), Instr::CallIndirect(rhs_call)) => {
                if lhs_call.ty != rhs_call.ty || lhs_call.table != rhs_call.table {
                    return false;
                }
            }
            (
                Instr::LocalGet(LocalGet { local: lhs }),
                Instr::LocalGet(LocalGet { local: rhs }),
            )
            | (
                Instr::LocalSet(LocalSet { local: lhs }),
                Instr::LocalSet(LocalSet { local: rhs }),
            )
            | (
                Instr::LocalTee(LocalTee { local: lhs }),
                Instr::LocalTee(LocalTee { local: rhs }),
            ) => {
                if locals_map.record(*lhs, *rhs) {
                    return false;
                }
            }
            (
                Instr::GlobalGet(GlobalGet { global: lhs }),
                Instr::GlobalGet(GlobalGet { global: rhs }),
            )
            | (
                Instr::GlobalSet(GlobalSet { global: lhs }),
                Instr::GlobalSet(GlobalSet { global: rhs }),
            ) => {
                if lhs != rhs {
                    return false;
                }
            }
            (Instr::Const(lhs), Instr::Const(rhs)) => {
                if !values_have_same_type(lhs.value, rhs.value) {
                    return false;
                }
            }
            (Instr::Binop(lhs), Instr::Binop(rhs)) => {
                if lhs.op != rhs.op {
                    return false;
                }
            }
            (Instr::Unop(lhs), Instr::Unop(rhs)) => {
                if lhs.op != rhs.op {
                    return false;
                }
            }
            (Instr::Select(lhs), Instr::Select(rhs)) => {
                if lhs.ty != rhs.ty {
                    return false;
                }
            }
            (Instr::Unreachable(_), Instr::Unreachable(_)) => {}
            (Instr::Br(Br { block: lhs }), Instr::Br(Br { block: rhs }))
            | (Instr::BrIf(BrIf { block: lhs }), Instr::BrIf(BrIf { block: rhs })) => {
                if seqs_map.record(*lhs, *rhs) {
                    return false;
                }
            }
            (Instr::IfElse(lhs), Instr::IfElse(rhs)) => {
                if seqs_map.record(lhs.consequent, rhs.consequent) {
                    return false;
                }
                if seqs_map.record(lhs.alternative, rhs.alternative) {
                    return false;
                }
            }
            (Instr::BrTable(lhs), Instr::BrTable(rhs)) => {
                for (lhs, rhs) in lhs.blocks.iter().zip(rhs.blocks.iter()) {
                    if seqs_map.record(*lhs, *rhs) {
                        return false;
                    }
                }
                if seqs_map.record(lhs.default, rhs.default) {
                    return false;
                }
            }
            (Instr::Drop(_), Instr::Drop(_)) => {}
            (Instr::Return(_), Instr::Return(_)) => {}
            (
                Instr::MemorySize(MemorySize { memory: lhs }),
                Instr::MemorySize(MemorySize { memory: rhs }),
            )
            | (
                Instr::MemoryGrow(MemoryGrow { memory: lhs }),
                Instr::MemoryGrow(MemoryGrow { memory: rhs }),
            ) => {
                if lhs != rhs {
                    return false;
                }
            }
            (Instr::MemoryInit(lhs), Instr::MemoryInit(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.data != rhs.data {
                    return false;
                }
            }
            (Instr::DataDrop(lhs), Instr::DataDrop(rhs)) => {
                if lhs.data != rhs.data {
                    return false;
                }
            }
            (Instr::MemoryCopy(lhs), Instr::MemoryCopy(rhs)) => {
                if lhs.src != rhs.src {
                    return false;
                }
                if lhs.dst != rhs.dst {
                    return false;
                }
            }
            (Instr::MemoryFill(lhs), Instr::MemoryFill(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
            }
            (Instr::Load(lhs), Instr::Load(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.kind != rhs.kind {
                    return false;
                }
                if lhs.arg != rhs.arg {
                    return false;
                }
            }
            (Instr::Store(lhs), Instr::Store(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.kind != rhs.kind {
                    return false;
                }
                if lhs.arg != rhs.arg {
                    return false;
                }
            }
            (Instr::AtomicRmw(lhs), Instr::AtomicRmw(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.op != rhs.op {
                    return false;
                }
                if lhs.width != rhs.width {
                    return false;
                }
                if lhs.arg != rhs.arg {
                    return false;
                }
            }
            (Instr::Cmpxchg(lhs), Instr::Cmpxchg(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.width != rhs.width {
                    return false;
                }
                if lhs.arg != rhs.arg {
                    return false;
                }
            }
            (Instr::AtomicNotify(lhs), Instr::AtomicNotify(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.arg != rhs.arg {
                    return false;
                }
            }
            (Instr::AtomicWait(lhs), Instr::AtomicWait(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.arg != rhs.arg {
                    return false;
                }
                if lhs.sixty_four != rhs.sixty_four {
                    return false;
                }
            }
            (Instr::AtomicFence(_), Instr::AtomicFence(_)) => {}
            (
                Instr::TableGet(TableGet { table: lhs }),
                Instr::TableGet(TableGet { table: rhs }),
            )
            | (
                Instr::TableSet(TableSet { table: lhs }),
                Instr::TableSet(TableSet { table: rhs }),
            )
            | (
                Instr::TableGrow(TableGrow { table: lhs }),
                Instr::TableGrow(TableGrow { table: rhs }),
            )
            | (
                Instr::TableSize(TableSize { table: lhs }),
                Instr::TableSize(TableSize { table: rhs }),
            )
            | (
                Instr::TableFill(TableFill { table: lhs }),
                Instr::TableFill(TableFill { table: rhs }),
            ) => {
                if lhs != rhs {
                    return false;
                }
            }
            (Instr::RefNull(lhs), Instr::RefNull(rhs)) => {
                if lhs.ty != rhs.ty {
                    return false;
                }
            }
            (Instr::RefIsNull(_), Instr::RefIsNull(_)) => {}
            (Instr::RefFunc(lhs), Instr::RefFunc(rhs)) => {
                if lhs.func != rhs.func {
                    return false;
                }
            }
            (Instr::V128Bitselect(_), Instr::V128Bitselect(_)) => {}
            (Instr::I8x16Swizzle(_), Instr::I8x16Swizzle(_)) => {}
            (Instr::I8x16Shuffle(lhs), Instr::I8x16Shuffle(rhs)) => {
                if lhs.indices != rhs.indices {
                    return false;
                }
            }
            (Instr::LoadSimd(lhs), Instr::LoadSimd(rhs)) => {
                if lhs.memory != rhs.memory {
                    return false;
                }
                if lhs.kind != rhs.kind {
                    return false;
                }
                if lhs.arg != rhs.arg {
                    return false;
                }
            }
            (Instr::TableInit(lhs), Instr::TableInit(rhs)) => {
                if lhs.table != rhs.table {
                    return false;
                }
                if lhs.elem != rhs.elem {
                    return false;
                }
            }
            (Instr::ElemDrop(lhs), Instr::ElemDrop(rhs)) => {
                if lhs.elem != rhs.elem {
                    return false;
                }
            }
            (Instr::TableCopy(lhs), Instr::TableCopy(rhs)) => {
                if lhs.src != rhs.src {
                    return false;
                }
                if lhs.dst != rhs.dst {
                    return false;
                }
            }
            (lhs_other, rhs_other) => {
                unimplemented!("check equality of {:?} and {:?}", lhs_other, rhs_other)
            }
        }
    }

    for (lhs_local, rhs_local) in locals_map.iter() {
        let lhs = module.locals.get(*lhs_local);
        let rhs = module.locals.get(*rhs_local);
        if lhs.ty() != rhs.ty() {
            return false;
        }
    }

    return true;
}

fn values_have_same_type(lhs: Value, rhs: Value) -> bool {
    match (lhs, rhs) {
        (Value::I32(_), Value::I32(_)) => true,
        (Value::I64(_), Value::I64(_)) => true,
        (Value::F32(_), Value::F32(_)) => true,
        (Value::F64(_), Value::F64(_)) => true,
        (_, _) => false,
    }
}

fn dfs_pre_order_iter<'instr>(
    func: &'instr LocalFunction,
    start: InstrSeqId,
) -> impl Iterator<Item = &'instr Instr> {
    use walrus::ir::{Block, Loop};
    struct Iter<'instr> {
        func: &'instr LocalFunction,
        seq_stack: Vec<InstrSeqId>,
        current_seq: Option<std::slice::Iter<'instr, (Instr, InstrLocId)>>,
    }
    impl<'instr> Iterator for Iter<'instr> {
        type Item = &'instr Instr;
        fn next(&mut self) -> Option<Self::Item> {
            fn next<'a>(
                seq: &mut std::slice::Iter<'a, (Instr, InstrLocId)>,
                seq_stack: &mut Vec<InstrSeqId>,
            ) -> Option<&'a Instr> {
                let instr = match seq.next().map(|(instr, _)| instr) {
                    Some(instr) => match instr {
                        Instr::Block(Block { seq }) | Instr::Loop(Loop { seq }) => {
                            seq_stack.push(*seq);
                            instr
                        }
                        Instr::IfElse(IfElse {
                            consequent,
                            alternative,
                        }) => {
                            seq_stack.push(*consequent);
                            seq_stack.push(*alternative);
                            instr
                        }
                        other => other,
                    },
                    None => return None,
                };
                Some(instr)
            }
            match self.current_seq.as_mut() {
                Some(seq) => next(seq, &mut self.seq_stack),
                None => {
                    let seq_id = match self.seq_stack.pop() {
                        Some(seq_id) => seq_id,
                        None => return None,
                    };
                    let mut seq = self.func.block(seq_id).iter();
                    let instr = next(&mut seq, &mut self.seq_stack);
                    self.current_seq.replace(seq);
                    instr
                }
            }
        }
    }
    Iter {
        func,
        seq_stack: vec![start],
        current_seq: None,
    }
}

#[cfg(test)]
mod tests {
    use walrus::{FunctionBuilder, ValType};

    use crate::merge::const_param::FunctionHash;

    fn create_func_hash(builder: FunctionBuilder, module: &mut walrus::Module) -> FunctionHash {
        let f = builder.finish(vec![], &mut module.funcs);
        let f1 = module.funcs.get(f).kind.unwrap_local();
        FunctionHash::hash_local(f1, &module)
    }

    #[test]
    fn test_func_hash() {
        let mut module = walrus::Module::default();

        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder.func_body().i32_const(42).drop();
        let f1_hash_value = create_func_hash(f1_builder, &mut module);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder.func_body().i64_const(42).drop();
        let f2_hash_value = create_func_hash(f2_builder, &mut module);

        assert_ne!(f1_hash_value, f2_hash_value, "const type");

        let mut f3_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f3_builder.func_body().i64_const(43).drop();
        let f3_hash_value = create_func_hash(f3_builder, &mut module);

        assert_eq!(f2_hash_value, f3_hash_value, "const value");

        let mut f4_builder = FunctionBuilder::new(&mut module.types, &[ValType::I32], &[]);
        f4_builder.func_body().i64_const(43).drop();
        let f4_hash_value = create_func_hash(f4_builder, &mut module);
        assert_ne!(f3_hash_value, f4_hash_value, "param type");
    }
}
