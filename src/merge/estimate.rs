use walrus::{Encoder, IdHashMap, LocalFunction};

struct Estimate {}

impl walrus::GetItemIndices for Estimate {
    fn get_memory_index(&self, _id: walrus::MemoryId) -> u32 {
        1
    }

    fn get_data_index(&self, _id: walrus::DataId) -> u32 {
        1
    }

    fn get_func_index(&self, _id: walrus::FunctionId) -> u32 {
        16383
    }

    fn get_type_index(&self, _id: walrus::TypeId) -> u32 {
        16383
    }

    fn get_table_index(&self, _id: walrus::TableId) -> u32 {
        1
    }

    fn get_global_index(&self, _id: walrus::GlobalId) -> u32 {
        1
    }

    fn get_element_index(&self, _id: walrus::ElementId) -> u32 {
        16383
    }
}

pub fn estimate_func_byte(f: &LocalFunction) -> usize {
    let estimate = Estimate {};
    let mut local_indices = IdHashMap::default();
    for local in f.used_locals() {
        local_indices.insert(local, 1);
    }
    let mut buffer = Vec::new();
    let mut encoder = Encoder::new(&mut buffer);
    walrus::module::run(f, &estimate, &local_indices, &mut encoder, None);
    buffer.len()
}
