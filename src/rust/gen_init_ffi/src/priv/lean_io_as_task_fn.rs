use leanh_l1::{
    datatypes::LeanObject,
    emitted::lean_box::lean_box,
    runtime_apply::lean_apply_1,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_io_task.rs:42-48

pub(crate) unsafe extern "C" fn lean_io_as_task_fn(
    act: *mut LeanObject,
    _world: *mut LeanObject,
) -> *mut LeanObject {
    lean_apply_1(act, lean_io_mk_world())
}

#[inline]
fn lean_io_mk_world() -> *mut LeanObject {
    unsafe { lean_box(0) }
}
