use leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};
use std::ffi::c_void;

// appended by move_rust_fn_to_leanh_l1_initializers.ts from ../lean4-rust/src/rust/lean_runtime/src/lib.rs:1817-1821

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn initialize_library_module() {
    unsafe { initialize_library_module_body() }
}

// appended by move_rust_fn_to_leanh_l1_initializers.ts from src/rust/leanh_l2/src/in_emit_rust.rs:113-116

pub fn initialize_library_module() {
    unsafe { initialize_library_module_body() }
}
