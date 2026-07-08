use crate::datatypes::{LeanTaskImp, LeanTaskObject};
use crate::emitted::lean_dec::lean_dec;
use crate::emitted::lean_dec_ref::lean_dec_ref;
use crate::r#priv::free_task::free_task;
use crate::runtime_object_task::task_manager::{TaskManager, TaskManagerInner};
use std::sync::atomic::Ordering;
use std::sync::{Arc, MutexGuard};

// ─── Helper: temporarily unlock a mutex guard ────────────────────────────

macro_rules! with_mutex_unlocked {
    ($guard:ident, $mutex:expr, $body:block) => {{
        unsafe {
            let p: *mut _ = $guard;
            core::ptr::drop_in_place(p);
            let _result = $body;
            let new_guard = $mutex.lock().unwrap();
            core::ptr::write(p, new_guard);
            _result
        }
    }};
}

pub(crate) use with_mutex_unlocked;
fn deactivate_task_core<'a>(
    slf: &'a Arc<TaskManager>,
    guard: &mut MutexGuard<'a, TaskManagerInner>,
    t: *mut LeanTaskObject,
) {
    let imp = unsafe { (*t).m_imp as *mut LeanTaskImp };
    let closure = unsafe { (*imp).m_closure };
    let mut it = unsafe { (*imp).m_head_dep };
    unsafe {
        (*imp).m_closure = core::ptr::null_mut();
        (*imp).m_head_dep = core::ptr::null_mut();
        (*imp).m_canceled = true;
        (*imp).m_deleted = true;
    }
    with_mutex_unlocked!(guard, slf.inner, {
        while !it.is_null() {
            let it_imp = (*it).m_imp as *mut LeanTaskImp;
            debug_assert!((*it_imp).m_deleted);
            let next = (*it_imp).m_next_dep;
            free_task(it);
            it = next;
        }
        if !closure.is_null() {
            lean_dec_ref(closure);
        }
    });
}

pub unsafe fn deactivate_task_obj(slf: &Arc<TaskManager>, t: *mut LeanTaskObject) {
    let mut guard = slf.inner.lock().unwrap();
    let v = unsafe { (*t).m_value.load(Ordering::Acquire) };
    if !v.is_null() {
        debug_assert!(unsafe { (*t).m_imp.is_null() });
        drop(guard);
        unsafe {
            lean_dec(v);
        }
        unsafe {
            free_task(t);
        }
        return;
    }
    debug_assert!(!unsafe { (*t).m_imp.is_null() });
    deactivate_task_core(slf, &mut guard, t);
}
