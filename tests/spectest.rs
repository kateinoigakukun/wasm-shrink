use std::path::Path;
use wasmtime::{Config, Engine, Store, Strategy};
use wasmtime_wast::WastContext;

include!(concat!(env!("OUT_DIR"), "/wast_testsuite_tests.rs"));

fn run_wast(wast: &str) -> anyhow::Result<()> {
    let wast = Path::new(wast);

    let mut cfg = Config::new();
    let simd = feature_found(wast, "simd");
    let memory64 = feature_found(wast, "memory64");
    let multi_memory = feature_found(wast, "multi-memory");
    let module_linking = feature_found(wast, "module-linking");
    let threads = feature_found(wast, "threads");
    let reftypes = simd || feature_found(wast, "reference-types");
    let bulk_mem = memory64 || multi_memory || feature_found(wast, "bulk-memory-operations");

    cfg.wasm_simd(simd)
        .wasm_bulk_memory(bulk_mem)
        .wasm_reference_types(reftypes || module_linking)
        .wasm_multi_memory(multi_memory || module_linking)
        .wasm_module_linking(module_linking)
        .wasm_threads(threads)
        .wasm_memory64(memory64)
        .strategy(Strategy::Cranelift)?
        .cranelift_debug_verifier(true);

    let store = Store::new(&Engine::new(&cfg)?, ());
    let mut wast_context = WastContext::new(store);
    wast_context.register_spectest()?;
    wast_context.run_file(wast)?;
    Ok(())
}

fn feature_found(path: &Path, name: &str) -> bool {
    path.iter().any(|part| match part.to_str() {
        Some(s) => s.contains(name),
        None => false,
    })
}
