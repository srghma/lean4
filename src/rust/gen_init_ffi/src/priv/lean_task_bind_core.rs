use leanh_l1::{
    datatypes::{LeanObject, LeanTaskObject},
    runtime_apply::lean_apply_1,
    runtime_object_task::{
        lean_task_get_own::lean_task_get_own, p1_get_task_manager::get_task_manager,
        p3_resolve::LEAN_SYNC_PRIO,
    },
};
use std::sync::atomic::Ordering;

use crate::r#priv::{
    add_task_dep::add_task_dep, alloc_running_task::alloc_running_task,
    mk_closure_3_2::mk_closure_3_2, task_bind_fn1::task_bind_fn1,
};

pub unsafe fn lean_task_bind_core(
    x: *mut LeanObject,
    f: *mut LeanObject,
    prio: u32,
    sync: bool,
    keep_alive: bool,
) -> *mut LeanObject {
    let task = x as *mut LeanTaskObject;
    if let Some(tm) = get_task_manager() {
        if sync && !(*task).m_value.load(Ordering::Acquire).is_null() {
            return lean_apply_1(f, lean_task_get_own(x));
        }
        let effective_prio = if sync { LEAN_SYNC_PRIO } else { prio };
        let closure = mk_closure_3_2(task_bind_fn1, x, f);
        let new_task = alloc_running_task(closure, effective_prio, keep_alive);
        add_task_dep(&tm, task, new_task);
        new_task as *mut LeanObject
    } else {
        lean_apply_1(f, lean_task_get_own(x))
    }
}
