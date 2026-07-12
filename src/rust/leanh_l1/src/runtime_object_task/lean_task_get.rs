use crate::datatypes::{LeanObject, LeanTaskImp, LeanTaskObject};
use crate::r#priv::lean_to_task::lean_to_task;
use crate::runtime_object_panic::lean_panic::lean_panic;
use crate::runtime_object_task::p3_resolve::{spawn_worker, LEAN_SYNC_PRIO};
use crate::runtime_object_task::scoped_current_task::current_task;
use crate::runtime_object_task::task_manager::{TaskManager, LEAN_MAX_PRIO};
use std::sync::atomic::Ordering;
use std::sync::Arc;

use crate::runtime_object_task::p1_get_task_manager::get_task_manager;

fn wait_for(slf: &Arc<TaskManager>, t: *mut LeanTaskObject) {
    if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
        return;
    }
    let mut guard = slf.inner.lock().unwrap();
    if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
        return;
    }

    let ct = current_task();
    let in_pool =
        !ct.is_null() && unsafe { (*((*ct).m_imp as *mut LeanTaskImp)).m_prio <= LEAN_MAX_PRIO };

    if !ct.is_null() {
        let ct_imp = unsafe { (*ct).m_imp as *mut LeanTaskImp };
        if unsafe { (*ct_imp).m_prio == LEAN_SYNC_PRIO } {
            unsafe {
                lean_panic("`Task.get` called from a `(sync := true)` task", false);
            }
        }
    }

    if in_pool {
        guard.max_std_workers += 1;
        if guard.idle_std_workers == 0 && guard.total_std_workers < guard.max_std_workers {
            spawn_worker(slf, &mut guard);
        } else {
            slf.queue_cv.notify_one();
        }
    }

    guard = slf
        .task_finished_cv
        .wait_while(guard, |_| unsafe {
            (*t).m_value.load(Ordering::Acquire).is_null()
        })
        .unwrap();

    if in_pool {
        guard.max_std_workers -= 1;
    }
}

pub unsafe fn lean_task_get(t: *mut LeanObject) -> *mut LeanObject {
    let task = lean_to_task(t);
    let v = unsafe { (*task).m_value.load(Ordering::Acquire) };
    if !v.is_null() {
        return v;
    }
    if let Some(tm) = get_task_manager() {
        wait_for(&tm, task as *mut LeanTaskObject);
    }
    let v2 = unsafe { (*task).m_value.load(Ordering::Acquire) };
    debug_assert!(!v2.is_null());
    v2
}
