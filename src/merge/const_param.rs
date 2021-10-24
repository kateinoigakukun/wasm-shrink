//! Constant Parameterization
//!
//! ## TODO
//! - Create thunk based on merge-benefit
//! - Merge functions bottom-up in call graph
//! - Allow direct callee difference

use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use walrus::ir::{
    Block, Br, BrIf, BrTable, Const, GlobalGet, GlobalSet, IfElse, Instr, InstrSeqId, InstrSeqType,
    LocalGet, LocalSet, LocalTee, Loop, MemoryGrow, MemorySize, TableFill, TableGet, TableGrow,
    TableSet, TableSize, Value, Visitor,
};
use walrus::{
    FunctionBuilder, FunctionId, InstrLocId, InstrSeqBuilder, LocalFunction, LocalId, ValType,
};

use crate::merge::call_graph::CallGraph;
use crate::merge::{func_hash, replace};

#[derive(PartialEq, Eq, Debug, Hash, Clone, Copy)]
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
        func_hash::run(f, module, &mut hasher);
        Self(hasher.finish())
    }
}

#[derive(Debug)]
struct EquivalenceClass {
    primary_func: FunctionId,
    /// List of functions belonging to a same class
    funcs: Vec<FunctionId>,
    hash: FunctionHash,
}

impl EquivalenceClass {
    fn primary_func<'module>(&self, module: &'module walrus::Module) -> &'module walrus::Function {
        module.funcs.get(self.primary_func)
    }
    fn is_eligible_to_merge(&self) -> bool {
        // ensure that this class has two funcs
        self.funcs.len() >= 2
    }

    fn thunk_func_name(&self, original: Option<&str>) -> Option<String> {
        match original {
            Some(name) => Some(format!("{}$merge_thunk", name)),
            None => None,
        }
    }

    fn remangle_merged_func(&self, module: &walrus::Module) -> Option<String> {
        for f in self.funcs.iter() {
            let f = module.funcs.get(*f);
            if let Some(name) = &f.name {
                return Some(format!("{}$merge_shared", name));
            }
        }
        None
    }
}

pub fn merge_funcs(module: &mut walrus::Module) {
    let mut call_graph = CallGraph::build_from(module);
    let fn_classes = collect_equivalence_class(module);

    log::debug!("Dump function equivalence classes");
    let mut mergable_funcs = 0;
    for class in fn_classes.iter() {
        if !class.is_eligible_to_merge() {
            continue;
        }
        log::debug!(
            "EC: primary={}, hash={:?}",
            class
                .primary_func(&module)
                .name
                .as_ref()
                .map(String::as_str)
                .unwrap_or("unknown"),
            class.hash
        );
        for fn_id in class.funcs.iter().skip(1) {
            let fn_entry = module.funcs.get(*fn_id);
            let name = fn_entry
                .name
                .as_ref()
                .map(String::as_str)
                .unwrap_or("unknown");
            log::debug!(" - {}", name);
        }
        mergable_funcs += class.funcs.len() - 1;
    }
    log::debug!("mergable_funcs = {}", mergable_funcs);

    for class in fn_classes {
        try_merge_equivalence_class(&class, module, &mut call_graph);
    }
}

fn collect_equivalence_class(module: &walrus::Module) -> Vec<EquivalenceClass> {
    let mut hashed_group: HashMap<FunctionHash, Vec<&walrus::Function>> = HashMap::new();
    // FIXME: This grouping can be done by O(NlogN) by using sort algorithm
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

    let mut fn_classes: Vec<EquivalenceClass> = vec![];

    for (key, group) in hashed_group {
        if group.len() < 2 {
            continue;
        }
        let mut classes: Vec<EquivalenceClass> = vec![EquivalenceClass {
            primary_func: group[0].id(),
            funcs: vec![],
            hash: key,
        }];

        for f in group {
            let mut found = false;
            for class in classes.iter_mut() {
                if are_in_equivalence_class(class.primary_func(module), f, &module) {
                    class.funcs.push(f.id());
                    found = true;
                    break;
                }
            }

            if !found {
                classes.push(EquivalenceClass {
                    primary_func: f.id(),
                    funcs: vec![],
                    hash: key,
                })
            }
        }
        fn_classes.append(&mut classes);
    }
    fn_classes
}

fn try_merge_equivalence_class(
    class: &EquivalenceClass,
    module: &mut walrus::Module,
    call_graph: &mut CallGraph,
) {
    let params = match derive_params(class, module) {
        Some(params) => params,
        None => {
            log::warn!("derive_params returns None unexpectedly for {:?}", class);
            return;
        }
    };

    if params.is_empty() {
        let mut thunk_map = HashMap::new();
        for from in class.funcs.iter().skip(1) {
            thunk_map.insert(*from, class.primary_func);
        }
        replace::replace_funcs(&thunk_map, module, call_graph);
        return;
    }

    let (original_param_tys, original_result_tys) = {
        let (params, results) = module.types.params_results(class.primary_func(module).ty());
        (params.to_vec(), results.to_vec())
    };

    let merged_func = create_merged_func(
        class.remangle_merged_func(&module),
        class.primary_func,
        &params,
        module,
    );
    call_graph.add_function(
        merged_func,
        module.funcs.get(merged_func).kind.unwrap_local(),
    );

    let params = params
        .0
        .into_iter()
        .map(|param| param.values)
        .collect::<Vec<_>>();

    let mut thunk_map = HashMap::new();

    for (idx, from) in class.funcs.iter().enumerate() {
        let name = module.funcs.get(*from).name.as_ref().map(String::as_str);
        let thunk_id = create_thunk_func(
            class.thunk_func_name(name),
            &original_param_tys,
            &original_result_tys,
            merged_func,
            &params,
            idx,
            module,
        );
        thunk_map.insert(*from, thunk_id);
        call_graph.add_function(thunk_id, module.funcs.get(thunk_id).kind.unwrap_local());
    }

    replace::replace_funcs(&thunk_map, module, call_graph);
}

struct ParamInfos(Vec<ParamInfo>);

impl Deref for ParamInfos {
    type Target = Vec<ParamInfo>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ParamInfos {
    fn find(&self, seq_id: InstrSeqId, position: usize) -> Option<(usize, &ParamInfo)> {
        for (pos, param) in self.0.iter().enumerate() {
            for param_use in &param.uses {
                if param_use.seq_id == seq_id && param_use.position == position {
                    return Some((pos, param));
                }
            }
        }
        None
    }
}

struct Cloner<'a> {
    iseq_type_map: HashMap<InstrSeqId, InstrSeqType>,
    builder: FunctionBuilder,
    /// `(original_iseq_id, new_iseq_id, position)`
    iseq_stack: Vec<(InstrSeqId, InstrSeqId, usize)>,
    /// `original` to `new` iseq id map
    iseq_map: HashMap<InstrSeqId, InstrSeqId>,

    params: &'a ParamInfos,
    /// The order should be matched with `params`
    extra_args: Vec<LocalId>,
}

impl<'a> Cloner<'a> {
    fn clone(
        name: Option<String>,
        original: FunctionId,
        params: &'a ParamInfos,
        module: &mut walrus::Module,
    ) -> FunctionId {
        let original = module.funcs.get(original);
        let original = original.kind.unwrap_local();

        let iseq_type_map = {
            #[derive(Default)]
            struct Collector {
                iseq_type_map: HashMap<InstrSeqId, InstrSeqType>,
            }
            impl<'instr> Visitor<'instr> for Collector {
                fn start_instr_seq(&mut self, instr_seq: &'instr walrus::ir::InstrSeq) {
                    self.iseq_type_map.insert(instr_seq.id(), instr_seq.ty);
                }
            }
            let mut collector = Collector::default();
            walrus::ir::dfs_in_order(&mut collector, original, original.entry_block());
            collector.iseq_type_map
        };

        let (param_types, result_types, extra_args) = {
            let (param_types, result_types) = module.types.params_results(original.ty());

            let result_types = result_types.to_vec();
            let mut param_types: Vec<ValType> = param_types.to_vec();
            let extra_params_types = params
                .iter()
                .map(|param| param.values.val_type())
                .collect::<Vec<_>>();
            param_types.append(&mut extra_params_types.clone());

            let mut extra_args = vec![];
            for ty in extra_params_types {
                extra_args.push(module.locals.add(ty));
            }
            (param_types, result_types, extra_args)
        };

        let mut builder = FunctionBuilder::new(&mut module.types, &param_types, &result_types);
        if let Some(name) = name {
            builder.name(name);
        }
        let mut iseq_map = HashMap::new();
        iseq_map.insert(original.entry_block(), builder.func_body_id());

        let mut cloner = Cloner {
            iseq_type_map,
            builder,
            iseq_stack: vec![],
            iseq_map,
            params,
            extra_args,
        };

        walrus::ir::dfs_in_order(&mut cloner, original, original.entry_block());
        let (builder, mut extra_args) = cloner.take();

        let mut new_args = original.args.clone();
        new_args.append(&mut extra_args);
        builder.finish(new_args, &mut module.funcs)
    }

    fn current_seq_id_and_pos(&self) -> &(InstrSeqId, InstrSeqId, usize) {
        self.iseq_stack.last().unwrap()
    }

    fn current_seq_id_and_pos_mut(&mut self) -> &mut (InstrSeqId, InstrSeqId, usize) {
        self.iseq_stack.last_mut().unwrap()
    }

    fn current_seq(&mut self) -> InstrSeqBuilder {
        let new_iseq_id = self.current_seq_id_and_pos().1;
        self.builder.instr_seq(new_iseq_id)
    }

    fn get_or_create_iseq_id(&mut self, original_iseq_id: &InstrSeqId) -> InstrSeqId {
        match self.iseq_map.get(original_iseq_id) {
            Some(new_iseq_id) => *new_iseq_id,
            None => {
                let iseq_ty = self.iseq_type_map.get(original_iseq_id).unwrap();
                let iseq_builder = self.builder.dangling_instr_seq(*iseq_ty);
                self.iseq_map.insert(*original_iseq_id, iseq_builder.id());
                iseq_builder.id()
            }
        }
    }

    fn take(self) -> (FunctionBuilder, Vec<LocalId>) {
        (self.builder, self.extra_args)
    }
}

impl<'instr> Visitor<'instr> for Cloner<'_> {
    fn start_instr_seq(&mut self, instr_seq: &'instr walrus::ir::InstrSeq) {
        let seq_builder_id = self.get_or_create_iseq_id(&instr_seq.id());
        self.builder.instr_seq(seq_builder_id);
        self.iseq_stack.push((instr_seq.id(), seq_builder_id, 0));
    }

    fn end_instr_seq(&mut self, _: &'instr walrus::ir::InstrSeq) {
        self.iseq_stack.pop();
    }

    fn visit_instr(&mut self, instr: &'instr Instr, _: &'instr InstrLocId) {
        let (original_seq_id, current_pos) = {
            let (original_seq_id, _, pos_mut) = self.current_seq_id_and_pos_mut();
            let current_pos = *pos_mut;
            let new_pos = current_pos + 1;
            *pos_mut = new_pos;
            (*original_seq_id, current_pos)
        };

        let new_instr = match (instr, self.params.find(original_seq_id, current_pos)) {
            (Instr::Const(_), Some((param_idx, _))) => {
                let arg = self.extra_args[param_idx];
                Instr::LocalGet(LocalGet { local: arg })
            }
            (_, Some(param)) => unimplemented!("unhandled param {:?}", param),
            (instr, None) => match instr {
                Instr::Block(Block { seq }) => {
                    let new_seq_id = self.get_or_create_iseq_id(seq);
                    Instr::Block(Block { seq: new_seq_id })
                }
                Instr::Loop(Loop { seq }) => {
                    let new_seq_id = self.get_or_create_iseq_id(seq);
                    Instr::Loop(Loop { seq: new_seq_id })
                }
                Instr::Br(Br { block }) => {
                    let new_seq_id = self.get_or_create_iseq_id(block);
                    Instr::Br(Br { block: new_seq_id })
                }
                Instr::BrIf(BrIf { block }) => {
                    let new_seq_id = self.get_or_create_iseq_id(block);
                    Instr::BrIf(BrIf { block: new_seq_id })
                }
                Instr::IfElse(IfElse {
                    consequent,
                    alternative,
                }) => {
                    let new_consequent = self.get_or_create_iseq_id(consequent);
                    let new_alternative = self.get_or_create_iseq_id(alternative);
                    Instr::IfElse(IfElse {
                        consequent: new_consequent,
                        alternative: new_alternative,
                    })
                }
                Instr::BrTable(BrTable { blocks, default }) => {
                    let new_blocks = blocks
                        .into_iter()
                        .map(|block| self.get_or_create_iseq_id(block))
                        .collect::<Box<[_]>>();
                    let new_default = self.get_or_create_iseq_id(default);
                    Instr::BrTable(BrTable {
                        blocks: new_blocks,
                        default: new_default,
                    })
                }
                other => other.clone(),
            },
        };

        self.current_seq().instr(new_instr.clone());
    }
}

fn create_merged_func(
    name: Option<String>,
    primary_func: FunctionId,
    params: &ParamInfos,
    module: &mut walrus::Module,
) -> walrus::FunctionId {
    Cloner::clone(name, primary_func, params, module)
}

fn create_thunk_func(
    name: Option<String>,
    original_param_tys: &[ValType],
    original_result_tys: &[ValType],
    merged_func: FunctionId,
    params: &[ConstDiff],
    idx: usize,
    module: &mut walrus::Module,
) -> FunctionId {
    let mut builder =
        FunctionBuilder::new(&mut module.types, original_param_tys, original_result_tys);
    if let Some(name) = name {
        builder.name(name);
    }
    let mut body = builder.func_body();

    let forwarding_args: Vec<LocalId> = original_param_tys
        .iter()
        .map(|ty| module.locals.add(*ty))
        .collect();

    for arg in forwarding_args.iter() {
        body.local_get(*arg);
    }

    for param in params {
        match param {
            ConstDiff::ConstI32(vs) => {
                let v = vs[idx];
                body.i32_const(v);
            }
            ConstDiff::ConstI64(vs) => {
                let v = vs[idx];
                body.i64_const(v);
            }
            ConstDiff::ConstF32(vs) => {
                let v = vs[idx];
                body.f32_const_exact(v);
            }
            ConstDiff::ConstF64(vs) => {
                let v = vs[idx];
                body.f64_const_exact(v);
            }
        }
    }

    body.call(merged_func);
    builder.finish(forwarding_args, &mut module.funcs)
}

#[derive(Debug)]
struct ParamInfo {
    /// const values ordered by the EquivalenceClass's `[primary_func] + funcs`
    values: ConstDiff,
    uses: Vec<InstrLocInfo>,
}

fn derive_params(class: &EquivalenceClass, module: &walrus::Module) -> Option<ParamInfos> {
    let primary_func = match &class.primary_func(module).kind {
        walrus::FunctionKind::Local(primary_func) => primary_func,
        _ => return None,
    };
    let mut primary_iter = dfs_pre_order_iter(&primary_func, primary_func.entry_block());
    let mut sibling_iters = vec![];

    // skip first primary func
    for func in class.funcs.iter().skip(1) {
        let func = module.funcs.get(*func);
        let func = match &func.kind {
            walrus::FunctionKind::Local(func) => func,
            _ => return None,
        };
        let iter = dfs_pre_order_iter(func, func.entry_block());
        sibling_iters.push(iter.map(|(instr, _)| instr));
    }

    let mut params: Vec<ParamInfo> = vec![];

    while let Some((primary_instr, loc)) = primary_iter.next() {
        let siblings = sibling_iters
            .iter_mut()
            .map(|iter| iter.next())
            .collect::<Option<Vec<&Instr>>>()?;

        let diff = match consts_diff(primary_instr, siblings) {
            Some(diff) => diff,
            None => continue,
        };

        {
            let mut found = false;
            for param in &mut params {
                if &param.values == &diff {
                    param.uses.push(loc);
                    found = true;
                    break;
                }
            }
            if !found {
                params.push(ParamInfo {
                    values: diff,
                    uses: vec![loc],
                });
            }
        }
    }
    Some(ParamInfos(params))
}

#[derive(Debug, PartialEq, Eq)]
enum ConstDiff {
    ConstI32(Vec<i32>),
    ConstI64(Vec<i64>),
    ConstF32(Vec<u32>),
    ConstF64(Vec<u64>),
}

impl ConstDiff {
    fn val_type(&self) -> ValType {
        match self {
            ConstDiff::ConstI32(_) => ValType::I32,
            ConstDiff::ConstI64(_) => ValType::I64,
            ConstDiff::ConstF32(_) => ValType::F32,
            ConstDiff::ConstF64(_) => ValType::F64,
        }
    }

    /// Return true if this diff can be omitted
    fn is_eligible_to_share(&self) -> bool {
        fn is_all_same<T: Eq>(vs: &Vec<T>) -> bool {
            let mut vs = vs.iter();
            if let Some(first) = vs.next() {
                vs.all(|v| v == first)
            } else {
                true
            }
        }
        match self {
            ConstDiff::ConstI32(vs) => is_all_same(vs),
            ConstDiff::ConstI64(vs) => is_all_same(vs),
            ConstDiff::ConstF32(vs) => is_all_same(vs),
            ConstDiff::ConstF64(vs) => is_all_same(vs),
        }
    }
}

fn consts_diff(primary: &Instr, siblings: Vec<&Instr>) -> Option<ConstDiff> {
    let primary_value = match primary {
        Instr::Const(Const { value }) => value,
        _ => return None,
    };

    let mut diff = match primary_value {
        Value::I32(v) => ConstDiff::ConstI32(vec![*v]),
        Value::I64(v) => ConstDiff::ConstI64(vec![*v]),
        Value::F32(v) => ConstDiff::ConstF32(vec![*v]),
        Value::F64(v) => ConstDiff::ConstF64(vec![*v]),
        Value::V128(_) => unimplemented!(),
    };

    for sibling in siblings {
        match (&mut diff, sibling) {
            (
                ConstDiff::ConstI32(values),
                Instr::Const(Const {
                    value: Value::I32(v),
                }),
            ) => values.push(*v),
            (
                ConstDiff::ConstI64(values),
                Instr::Const(Const {
                    value: Value::I64(v),
                }),
            ) => values.push(*v),
            (
                ConstDiff::ConstF32(values),
                Instr::Const(Const {
                    value: Value::F32(v),
                }),
            ) => values.push(*v),
            (
                ConstDiff::ConstF64(values),
                Instr::Const(Const {
                    value: Value::F64(v),
                }),
            ) => values.push(*v),
            _ => return None,
        }
    }

    if diff.is_eligible_to_share() {
        return None;
    }

    Some(diff)
}

/// Note that this comparator should satisfy transitivity
/// are_in_equivalence_class(A, B) && are_in_equivalence_class(B, C) -> are_in_equivalence_class(A, C)
fn are_in_equivalence_class(
    lhs: &walrus::Function,
    rhs: &walrus::Function,
    module: &walrus::Module,
) -> bool {
    let (lhs, rhs) = match (&lhs.kind, &rhs.kind) {
        (walrus::FunctionKind::Local(lhs), walrus::FunctionKind::Local(rhs)) => (lhs, rhs),
        _ => return false,
    };
    if lhs.ty() != rhs.ty() {
        return false;
    }

    let mut lhs_iter = dfs_pre_order_iter(&lhs, lhs.entry_block());
    let mut rhs_iter = dfs_pre_order_iter(&rhs, rhs.entry_block());

    struct IdPairMap<Id> {
        lhs_to_rhs: HashMap<Id, Id>,
    }

    impl<Id> Deref for IdPairMap<Id> {
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

    let mut locals_map = IdPairMap::<LocalId>::new();
    let mut seqs_map = IdPairMap::<InstrSeqId>::new();

    loop {
        let ((lhs_instr, _), (rhs_instr, _)) = match (lhs_iter.next(), rhs_iter.next()) {
            (None, None) => break,
            (Some(lhs), Some(rhs)) => (lhs, rhs),
            _ => return false,
        };
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

    for (lhs_local_id, rhs_local_id) in locals_map.iter() {
        let lhs_local = module.locals.get(*lhs_local_id);
        let rhs_local = module.locals.get(*rhs_local_id);
        if lhs_local.ty() != rhs_local.ty() {
            return false;
        }
        let lhs_idx = lhs.args.iter().position(|id| id == lhs_local_id);
        let rhs_idx = rhs.args.iter().position(|id| id == rhs_local_id);
        if lhs_idx != rhs_idx {
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

#[derive(Debug, Clone, Copy)]
struct InstrLocInfo {
    seq_id: InstrSeqId,
    loc_id: InstrLocId,
    position: usize,
}

fn dfs_pre_order_iter<'instr>(
    func: &'instr LocalFunction,
    start: InstrSeqId,
) -> impl Iterator<Item = (&'instr Instr, InstrLocInfo)> {
    type InstrIter<'instr> = std::iter::Enumerate<std::slice::Iter<'instr, (Instr, InstrLocId)>>;

    struct Iter<'instr> {
        func: &'instr LocalFunction,
        seq_stack: Vec<InstrSeqId>,
        current_seq: Option<(InstrIter<'instr>, InstrSeqId)>,
    }
    impl<'instr> Iterator for Iter<'instr> {
        type Item = (&'instr Instr, InstrLocInfo);
        fn next(&mut self) -> Option<Self::Item> {
            fn next_from_seq<'a>(
                seq: &mut InstrIter<'a>,
                seq_id: InstrSeqId,
                seq_stack: &mut Vec<InstrSeqId>,
            ) -> Option<(&'a Instr, InstrLocInfo)> {
                let instr = match seq.next() {
                    Some((position, (instr, loc))) => {
                        let instr = match instr {
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
                        };
                        (
                            instr,
                            InstrLocInfo {
                                seq_id,
                                loc_id: *loc,
                                position,
                            },
                        )
                    }
                    None => return None,
                };
                Some(instr)
            }
            if let Some((seq, seq_id)) = self.current_seq.as_mut() {
                if let Some(instr) = next_from_seq(seq, *seq_id, &mut self.seq_stack) {
                    return Some(instr);
                }
            }

            let seq_id = match self.seq_stack.pop() {
                Some(seq_id) => seq_id,
                None => return None,
            };
            let mut seq = self.func.block(seq_id).iter().enumerate();
            let instr = next_from_seq(&mut seq, seq_id, &mut self.seq_stack);
            self.current_seq.replace((seq, seq_id));
            instr
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
    use std::{
        collections::HashSet,
        path::{Path, PathBuf},
    };

    use walrus::{FunctionBuilder, ValType};

    use crate::merge::const_param::{self, *};

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

    #[test]
    fn test_are_in_equivalence_class_0() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder.func_body().i32_const(42).drop();
        let f1_id = f1_builder.finish(vec![], &mut module.funcs);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder.func_body().i32_const(43).drop();
        let f2_id = f2_builder.finish(vec![], &mut module.funcs);

        assert!(are_in_equivalence_class(
            module.funcs.get(f1_id),
            module.funcs.get(f2_id),
            &module
        ));
    }
    #[test]
    fn test_are_in_equivalence_class_1() {
        let mut module = walrus::Module::default();
        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder.func_body().i32_const(43).drop();
        let f2_id = f2_builder.finish(vec![], &mut module.funcs);

        let mut f3_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f3_builder
            .func_body()
            .i32_const(43)
            .drop()
            .i32_const(24)
            .drop();
        let f3_id = f3_builder.finish(vec![], &mut module.funcs);
        assert!(!are_in_equivalence_class(
            module.funcs.get(f2_id),
            module.funcs.get(f3_id),
            &module
        ));
    }

    #[test]
    fn test_are_in_equivalence_class_2() {
        let mut module = walrus::Module::default();
        let mut f4_builder = FunctionBuilder::new(
            &mut module.types,
            &[ValType::I32, ValType::I32],
            &[ValType::I32],
        );
        let arg0 = module.locals.add(ValType::I32);
        let arg1 = module.locals.add(ValType::I32);
        f4_builder.func_body().local_get(arg0);
        let f4_id = f4_builder.finish(vec![arg0, arg1], &mut module.funcs);

        let mut f5_builder = FunctionBuilder::new(
            &mut module.types,
            &[ValType::I32, ValType::I32],
            &[ValType::I32],
        );
        let arg0 = module.locals.add(ValType::I32);
        let arg1 = module.locals.add(ValType::I32);
        f5_builder.func_body().local_get(arg1);
        let f5_id = f5_builder.finish(vec![arg0, arg1], &mut module.funcs);
        assert!(!are_in_equivalence_class(
            module.funcs.get(f4_id),
            module.funcs.get(f5_id),
            &module
        ));
    }

    #[test]
    fn test_collect_equivalence_class() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder.func_body().i32_const(42).drop();
        let f1_id = f1_builder.finish(vec![], &mut module.funcs);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder.func_body().i32_const(43).drop();
        let f2_id = f2_builder.finish(vec![], &mut module.funcs);

        let classes = collect_equivalence_class(&module);
        assert_eq!(classes.len(), 1);

        let class = classes.get(0).unwrap();
        let mut func_ids: HashSet<_> = class.funcs.iter().collect();
        func_ids.insert(&class.primary_func);

        assert_eq!(func_ids, vec![f1_id, f2_id].iter().collect());
    }

    #[test]
    fn test_derive_params() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder.func_body().i32_const(42).drop();
        f1_builder.finish(vec![], &mut module.funcs);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder.func_body().i32_const(43).drop();
        f2_builder.finish(vec![], &mut module.funcs);

        let classes = collect_equivalence_class(&module);
        let class = classes.get(0).unwrap();

        let params = derive_params(class, &module).unwrap();
        assert_eq!(params.len(), 1);
        let param = params.get(0).unwrap();
        assert_eq!(param.uses.len(), 1);
        let param_use = param.uses.get(0).unwrap();
        assert_eq!(param_use.position, 0);
        assert_eq!(
            param_use.seq_id,
            class
                .primary_func(&module)
                .kind
                .unwrap_local()
                .entry_block()
        );
    }

    #[test]
    fn test_dfs_pre_order_iter() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[ValType::F64]);
        f1_builder.func_body().block(ValType::F64, |b| {
            b.f32_const(1.0);
        });
        let f1 = f1_builder.finish(vec![], &mut module.funcs);
        let f1 = module.funcs.get(f1).kind.unwrap_local();
        let iter = dfs_pre_order_iter(f1, f1.entry_block());
        let instrs = iter.collect::<Vec<_>>();
        assert_eq!(instrs.len(), 2, "not enough instrs '{:?}'", instrs);
    }

    #[test]
    fn test_derive_params_duplicated() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder
            .func_body()
            .i32_const(42)
            .drop()
            .i32_const(42)
            .drop();
        f1_builder.finish(vec![], &mut module.funcs);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder
            .func_body()
            .i32_const(43)
            .drop()
            .i32_const(43)
            .drop();
        f2_builder.finish(vec![], &mut module.funcs);

        let classes = collect_equivalence_class(&module);
        let class = classes.get(0).unwrap();

        let params = derive_params(class, &module).unwrap();
        assert_eq!(params.len(), 1);
        let param = params.get(0).unwrap();
        assert_eq!(param.uses.len(), 2);
        let param_positions: Vec<_> = param.uses.iter().map(|u| u.position).collect();
        assert_eq!(param_positions, vec![0, 2]);
    }

    #[test]
    fn test_derive_params_shared_const() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder
            .func_body()
            .i32_const(43) // should be shared
            .drop()
            .i32_const(42)
            .drop();
        f1_builder.finish(vec![], &mut module.funcs);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder
            .func_body()
            .i32_const(43) // should be shared
            .drop()
            .i32_const(43)
            .drop();
        f2_builder.finish(vec![], &mut module.funcs);

        let classes = collect_equivalence_class(&module);
        let class = classes.get(0).unwrap();

        let params = derive_params(class, &module).unwrap();
        assert_eq!(params.len(), 1);
        let param = params.get(0).unwrap();
        assert_eq!(param.uses.len(), 1);
    }

    #[test]
    fn test_func_cloner() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder.func_body().i32_const(42).drop();
        f1_builder.finish(vec![], &mut module.funcs);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder.func_body().i32_const(43).drop();
        f2_builder.finish(vec![], &mut module.funcs);

        let classes = collect_equivalence_class(&module);
        let class = classes.get(0).unwrap();

        let params = derive_params(class, &module).unwrap();
        let merged = create_merged_func(None, class.primary_func, &params, &mut module);

        let merged = module.funcs.get(merged);
        let merged_params = module.types.params(merged.ty());
        assert_eq!(merged_params, &[ValType::I32]);

        let merged = merged.kind.unwrap_local();
        let instrs = merged.block(merged.entry_block());
        assert_eq!(instrs.len(), 2);
        let (replaced_instr, _) = instrs.get(0).unwrap();

        assert_eq!(
            &replaced_instr.unwrap_local_get().local,
            merged.args.get(0).unwrap()
        );
    }

    #[test]
    fn test_create_thunk_unit() {
        let mut module = walrus::Module::default();
        let mut merged = FunctionBuilder::new(
            &mut module.types,
            &[ValType::I32, ValType::I32],
            &[ValType::I32],
        );
        let arg = module.locals.add(ValType::I32);
        let parameterized = module.locals.add(ValType::I32);
        merged.func_body().local_get(parameterized);

        let merged_func = merged.finish(vec![arg, parameterized], &mut module.funcs);

        let params = vec![ConstDiff::ConstI32(vec![42])];
        let thunk = create_thunk_func(
            None,
            &[ValType::I32],
            &[ValType::I32],
            merged_func,
            &params,
            0,
            &mut module,
        );
        let thunk = module.funcs.get(thunk).kind.unwrap_local();
        let thunk_params = module.types.params(thunk.ty());
        assert_eq!(thunk_params, &[ValType::I32]);

        let instrs = thunk.block(thunk.entry_block());
        assert_eq!(instrs.len(), 3);

        let (instr, _) = instrs.get(0).unwrap();
        assert_eq!(&instr.unwrap_local_get().local, thunk.args.get(0).unwrap());

        let (instr, _) = instrs.get(1).unwrap();
        assert_eq!(instr.unwrap_const().value, Value::I32(42));
    }

    #[test]
    fn test_merge_funcs_0() {
        let mut module = walrus::Module::default();
        let mut f1_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f1_builder.func_body().i32_const(42).drop();
        f1_builder.finish(vec![], &mut module.funcs);

        let mut f2_builder = FunctionBuilder::new(&mut module.types, &[], &[]);
        f2_builder.func_body().i32_const(43).drop();
        f2_builder.finish(vec![], &mut module.funcs);

    }

    fn find_tool<P>(exe_name: P) -> Option<PathBuf>
    where
        P: AsRef<Path>,
    {
        std::env::var_os("PATH").and_then(|paths| {
            std::env::split_paths(&paths)
                .filter_map(|dir| {
                    let full_path = dir.join(&exe_name);
                    if full_path.is_file() {
                        Some(full_path)
                    } else {
                        None
                    }
                })
                .next()
        })
    }

    fn check_no_crash(file: &str) {
        let fixture = PathBuf::from(file!())
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("tracker/fixture");
        let source = fixture.join(file);
        let result = fixture.join(format!("{}.opt", file));
        let mut module = walrus::Module::from_file(source).unwrap();
        const_param::merge_funcs(&mut module);
        module.emit_wasm_file(result.clone()).unwrap();

        if let Some(wasm2wat) = find_tool("wasm2wat") {
            let wat_output = fixture.join(format!("{}.opt.wat", file));
            std::process::Command::new(wasm2wat)
                .arg(result)
                .arg("-o")
                .arg(wat_output)
                .spawn()
                .unwrap()
                .wait()
                .unwrap();
        }
    }

    #[test]
    fn test_merge_simple() {
        check_no_crash("simple.wasm")
    }

    #[test]
    fn test_merge_large_complex() {
        check_no_crash("swift-hello.wasm")
    }

    #[test]
    fn test_merge_0() {
        check_no_crash("0.wasm")
    }
}
