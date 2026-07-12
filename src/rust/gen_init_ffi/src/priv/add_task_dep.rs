use leanh_l1::{
    datatypes::{LeanTaskImp, LeanTaskObject},
    runtime_object_task::{p3_resolve::enqueue_core, task_manager::TaskManager},
};
use std::sync::{Arc, atomic::Ordering};

use crate::r#priv::enqueue_task::enqueue_task;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_object_task.rs:21-41

// ─── Closure helpers ──────────────────────────────────────────────────────

pub(crate) fn add_task_dep(
    tm: &Arc<TaskManager>,
    t1: *mut LeanTaskObject,
    t2: *mut LeanTaskObject,
) {
    if !unsafe { (*t1).m_value.load(Ordering::Acquire).is_null() } {
        enqueue_task(tm, t2);
        return;
    }
    let mut guard = tm.inner.lock().unwrap();
    if !unsafe { (*t1).m_value.load(Ordering::Acquire).is_null() } {
        unsafe { enqueue_core(tm, &mut guard, t2) };
        return;
    }
    unsafe {
        let t2_imp = (*t2).m_imp as *mut LeanTaskImp;
        let t1_imp = (*t1).m_imp as *mut LeanTaskImp;
        (*t2_imp).m_next_dep = (*t1_imp).m_head_dep;
        (*t1_imp).m_head_dep = t2;
    }
}
