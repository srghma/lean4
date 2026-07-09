use leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};
use std::ffi::c_void;

// appended by move_rust_fn_to_leanh_l1_initializers.ts from src/rust/leanh_l2/src/in_emit_rust.rs:113-119

pub fn initialize_kernel_module() {
    initialize_type_checker();
    initialize_local_ctx();
    initialize_inductive();
    initialize_quot();
}
