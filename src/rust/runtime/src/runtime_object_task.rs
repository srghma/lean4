/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

pub(crate) mod runtime_object_task_impl {
    use crate::runtime_object_panic_impl::lean_internal_panic;
    use crate::runtime_object_rc_impl::{lean_alloc_small_object, lean_free_small_object};
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::sync::atomic::Ordering;
    use leanh::LeanTaskImp;
    use std::collections::VecDeque;
    use std::mem::MaybeUninit;
    use std::sync::{Arc, Condvar, Mutex, MutexGuard};
    use std::thread::JoinHandle;

    // ─── Constants ────────────────────────────────────────────────────────────

    use leanh::{LEAN_CLOSURE_TAG, LEAN_PROMISE_TAG, LEAN_TASK_TAG};

    fn wait_any(tm: &Arc<TaskManager>, task_list: *mut LeanObject) -> *mut LeanObject {
        if let Some(t) = wait_any_check(task_list) {
            return t;
        }
        let mut guard = tm.inner.lock().unwrap();
        loop {
            if let Some(t) = wait_any_check(task_list) {
                return t;
            }
            guard = tm.task_finished_cv.wait(guard).unwrap();
        }
    }

    fn wait_any_check(task_list: *mut LeanObject) -> Option<*mut LeanObject> {
        let mut it = task_list;
        while unsafe { !lean_is_scalar(it) } {
            let head = unsafe { lean_ctor_get(it, 0) };
            let task = head as *mut LeanTaskObject;
            if !unsafe { (*task).value.load(Ordering::Acquire).is_null() } {
                return Some(head);
            }
            it = unsafe { lean_ctor_get(it, 1) };
        }
        None
    }

    fn cancel_task(tm: &Arc<TaskManager>, t: *mut LeanTaskObject) {
        let _guard = tm.inner.lock().unwrap();
        let imp = unsafe { (*t).imp as *mut LeanTaskImp };
        if !imp.is_null() {
            unsafe {
                (*imp).m_canceled = true;
            }
        }
    }

    fn get_task_state(tm: &Arc<TaskManager>, t: *mut LeanTaskObject) -> u8 {
        let _guard = tm.inner.lock().unwrap();
        let imp = unsafe { (*t).imp as *mut LeanTaskImp };
        if imp.is_null() {
            return 2; // finished
        }
        if unsafe { (*imp).m_closure.is_null() } {
            return 1; // running / promised
        }
        0 // waiting / queued
    }

    fn is_shutting_down(tm: &TaskManager) -> bool {
        tm.inner.lock().unwrap().shutting_down
    }

    // ─── Init / finalize task manager ────────────────────────────────────────

    pub fn lean_init_task_manager_using(num_workers: usize) {
        debug_assert!(get_task_manager().is_none());
        #[cfg(lean_multi_thread)]
        if num_workers > 0 {
            set_task_manager(Some(new_task_manager(num_workers)));
        }
        #[cfg(not(lean_multi_thread))]
        let _ = num_workers;
    }

    // ─── IO task helpers ──────────────────────────────────────────────────────

    pub fn lean_io_check_canceled_core() -> bool {
        let ct = current_task();
        if ct.is_null() {
            return false;
        }
        unsafe {
            let imp = (*ct).imp as *mut LeanTaskImp;
            debug_assert!(!imp.is_null());
            if (*imp).m_canceled {
                return true;
            }
        }
        get_task_manager()
            .map(|tm| is_shutting_down(&tm))
            .unwrap_or(false)
    }

    pub unsafe fn lean_io_cancel_core(t: *mut LeanObject) {
        let task = t as *mut LeanTaskObject;
        if !(*task).value.load(Ordering::Acquire).is_null() {
            return;
        }
        if let Some(tm) = get_task_manager() {
            cancel_task(&tm, task);
        }
    }

    pub unsafe fn lean_io_get_task_state_core(t: *const LeanObject) -> u8 {
        let task = t as *mut LeanTaskObject;
        if (*task).imp.is_null() {
            return 2; // finished
        }
        if let Some(tm) = get_task_manager() {
            get_task_state(&tm, task)
        } else {
            2
        }
    }

    pub unsafe fn lean_io_wait_any_core(task_list: *mut LeanObject) -> *mut LeanObject {
        if let Some(tm) = get_task_manager() {
            wait_any(&tm, task_list)
        } else {
            wait_any_check(task_list).unwrap_or(core::ptr::null_mut())
        }
    }

    // ─── Deactivate task / promise (called from runtime_object_rc.rs) ─────────

    // ─── Promise new / resolve ────────────────────────────────────────────────

    // lean::lean_promise_new (C++ namespace → mangled name)
    pub unsafe fn lean_promise_new_impl() -> *mut LeanObject {
        if get_task_manager().is_none() {
            lean_internal_panic(
                c"`IO.Promise.new` called before the task manager is running; \
                  this typically happens when called (directly or transitively, \
                  e.g. via `IO.CancelToken.new`) from an `initialize` block. \
                  Construct lazily on first use instead."
                    .as_ptr() as *const i8,
            );
        }

        // Allocate the underlying task (no closure, no value yet).
        let t =
            lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
        set_task_header_mt(t as *mut LeanObject);
        (*t).value = AtomicPtr::new(core::ptr::null_mut());
        (*t).imp = alloc_task_imp(core::ptr::null_mut(), 0, false) as *mut c_void;

        // Allocate the promise wrapper.
        let o = lean_alloc_small_object(core::mem::size_of::<LeanPromiseObject>())
            as *mut LeanPromiseObject;
        (*o).header.rc = 1;
        (*o).header.other = 0;
        (*o).header.tag = LEAN_PROMISE_TAG;
        (*o).header.cs_size = 0;
        (*o).result = t as *mut LeanObject;

        o as *mut LeanObject
    }

    // lean::lean_promise_resolve (C++ namespace → mangled name)
    pub unsafe fn lean_promise_resolve_impl(value: *mut LeanObject, promise: *mut LeanObject) {
        let p = promise as *mut LeanPromiseObject;
        if let Some(tm) = get_task_manager() {
            let some_value = mk_option_some(value);
            tm.resolve((*p).result as *mut LeanTaskObject, some_value);
        }
    }

    pub unsafe fn lean_io_promise_new() -> *mut LeanObject {
        lean_promise_new_impl()
    }

    pub unsafe fn lean_io_promise_resolve(
        value: *mut LeanObject,
        promise: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_promise_resolve_impl(value, promise);
        lean_box(0)
    }

    pub unsafe fn lean_io_promise_result_opt(promise: *mut LeanObject) -> *mut LeanObject {
        let p = promise as *mut LeanPromiseObject;
        let t = (*p).result;
        lean_inc_ref(t);
        t
    }

    // ─── lean_get_or_block (IO.getOrBlock) ────────────────────────────────────

    pub unsafe fn lean_get_or_block(opt: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(opt) || (*opt).tag == 0 {
            lean_dec(opt);
            lean_box(0)
        } else {
            let task = lean_ctor_get(opt, 0);
            lean_inc(task);
            lean_dec(opt);
            let v = lean_task_get(task);
            lean_inc(v);
            lean_dec_ref(task);
            v
        }
    }
}

// Re-export functions needed by other modules (accessed via `use super::*`).
pub use runtime_object_task_impl::lean_io_get_task_state_core;
pub use runtime_object_task_impl::lean_task_get;
