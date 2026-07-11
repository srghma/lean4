use leanh_l1::{
    datatypes::LeanObject, emitted::lean_box::lean_box, runtime_apply::lean_apply_1,
    runtime_object_task::p1_get_task_manager::get_task_manager,
};

use crate::{
    ffi::Init::Core::lean_task_pure,
    r#priv::{alloc_running_task::alloc_running_task, enqueue_task::enqueue_task},
};

// ─── Task spawn ───────────────────────────────────────────────────────────

pub unsafe fn lean_task_spawn_core(
    c: *mut LeanObject,
    prio: u32,
    keep_alive: bool,
) -> *mut LeanObject {
    if let Some(tm) = get_task_manager() {
        let t = alloc_running_task(c, prio, keep_alive);
        enqueue_task(&tm, t);
        t as *mut LeanObject
    } else {
        lean_task_pure(lean_apply_1(c, lean_box(0)))
    }
}
