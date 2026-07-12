use leanh_l1::runtime_object_task::task_manager::TaskManager;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_object_task.rs:69-72

pub(crate) fn is_shutting_down(tm: &TaskManager) -> bool {
    tm.inner.lock().unwrap().shutting_down
}
