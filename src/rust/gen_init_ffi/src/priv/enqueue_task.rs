use leanh_l1::{
    datatypes::LeanTaskObject,
    runtime_object_task::{p3_resolve::enqueue_core, task_manager::TaskManager},
};
use std::sync::Arc;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_object_task.rs:66-70

pub(crate) fn enqueue_task(tm: &Arc<TaskManager>, t: *mut LeanTaskObject) {
    let mut guard = tm.inner.lock().unwrap();
    unsafe { enqueue_core(tm, &mut guard, t) };
}
