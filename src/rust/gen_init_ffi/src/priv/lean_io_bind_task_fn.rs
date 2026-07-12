use leanh_l1::datatypes::{LeanExternalObject, LeanObject, LeanScalarArray, LeanStringObject};
use std::ffi::c_void;

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_io_task.rs:49-55

pub(crate) unsafe extern "C" fn lean_io_bind_task_fn(
    f: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    lean_apply_2(f, a, lean_io_mk_world())
}

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_io_task.rs:7-10

pub(crate) unsafe fn lean_io_bind_task_fn(
    f: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    lean_apply_2(f, a, lean_io_mk_world())
}
