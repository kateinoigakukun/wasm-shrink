//! Constant Parameterization

use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;

use walrus::ir::{Visitor, VisitorMut};

struct FunctionHash(u64);

impl FunctionHash {
    fn hash(f: walrus::Function) -> Self {
        let mut hasher = DefaultHasher::new();
        Self(hasher.finish())
    }
}

pub fn merge_funcs(module: &mut walrus::Module) {
    unimplemented!()
}