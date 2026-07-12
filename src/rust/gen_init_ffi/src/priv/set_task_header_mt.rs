use leanh_l1::datatypes::{LeanObject, LeanObjectTag};

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_task.rs:157-167 and from src/rust/runtime/src/runtime_object_task.rs:66-76

// ─── Task header helpers ──────────────────────────────────────────────────

// Set the header for a multi-thread (rc = -1) task object.
#[inline(always)]
pub(crate) unsafe fn set_task_header_mt(o: *mut LeanObject) {
    (*o).rc = -1;
    (*o).tag = LeanObjectTag::Task.as_u8();
    (*o).other = 0;
    (*o).cs_size = 0;
}
