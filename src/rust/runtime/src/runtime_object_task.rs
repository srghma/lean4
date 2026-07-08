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

    // ─── Closure helpers ──────────────────────────────────────────────────────

    #[inline(always)]
    unsafe fn local_alloc_closure(fun: *mut c_void, arity: u32, num_fixed: u32) -> *mut LeanObject {
        let byte_size = core::mem::size_of::<LeanClosureLocal>()
            + core::mem::size_of::<*mut LeanObject>() * num_fixed as usize;
        let obj = lean_alloc_object(byte_size) as *mut LeanClosureLocal;
        (*obj).header.rc = 1;
        (*obj).header.other = 0;
        (*obj).header.tag = LEAN_CLOSURE_TAG;
        (*obj).header.cs_size = 0;
        (*obj).fun = fun;
        (*obj).arity = arity as u16;
        (*obj).num_fixed = num_fixed as u16;
        obj as *mut LeanObject
    }

    #[inline(always)]
    unsafe fn local_closure_set(o: *mut LeanObject, i: usize, v: *mut LeanObject) {
        let c = o as *mut LeanClosureLocal;
        *(*c).data.as_mut_ptr().add(i) = v;
    }

    #[inline(always)]
    unsafe fn mk_closure_2_1(
        fun: unsafe fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        let c = local_alloc_closure(fun as *mut c_void, 2, 1);
        local_closure_set(c, 0, a);
        c
    }

    #[inline(always)]
    unsafe fn mk_closure_3_2(
        fun: unsafe fn(*mut LeanObject, *mut LeanObject, *mut LeanObject) -> *mut LeanObject,
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let c = local_alloc_closure(fun as *mut c_void, 3, 2);
        local_closure_set(c, 0, a1);
        local_closure_set(c, 1, a2);
        c
    }

    // ─── Task header helpers ──────────────────────────────────────────────────

    // Set the header for a multi-thread (rc = -1) task object.
    #[inline(always)]
    unsafe fn set_task_header_mt(o: *mut LeanObject) {
        (*o).rc = -1;
        (*o).tag = LEAN_TASK_TAG;
        (*o).other = 0;
        (*o).cs_size = 0;
    }

    // Set the header for a single-thread (rc = 1) task object.
    #[inline(always)]
    unsafe fn set_task_header_st(o: *mut LeanObject) {
        (*o).rc = 1;
        (*o).tag = LEAN_TASK_TAG;
        (*o).other = 0;
        (*o).cs_size = 0;
    }

    // ─── Task allocation helpers ──────────────────────────────────────────────

    unsafe fn alloc_task_imp(
        closure: *mut LeanObject,
        prio: u32,
        keep_alive: bool,
    ) -> *mut LeanTaskImp {
        let imp = lean_alloc_small_object(core::mem::size_of::<LeanTaskImp>()) as *mut LeanTaskImp;
        (*imp).m_closure = closure;
        (*imp).m_head_dep = core::ptr::null_mut();
        (*imp).m_next_dep = core::ptr::null_mut();
        (*imp).m_prio = prio;
        (*imp).m_canceled = false;
        (*imp).m_keep_alive = keep_alive;
        (*imp).m_deleted = false;
        imp
    }

    // Allocate a running task (has closure, no value yet, MT header).
    unsafe fn alloc_running_task(
        closure: *mut LeanObject,
        prio: u32,
        keep_alive: bool,
    ) -> *mut LeanTaskObject {
        lean_mark_mt(closure);
        let o =
            lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
        set_task_header_mt(o as *mut LeanObject);
        (*o).value = AtomicPtr::new(core::ptr::null_mut());
        (*o).imp = alloc_task_imp(closure, prio, keep_alive) as *mut c_void;
        if keep_alive {
            lean_inc_ref(o as *mut LeanObject);
        }
        o
    }

    pub unsafe fn lean_task_pure(value: *mut LeanObject) -> *mut LeanObject {
        let o =
            lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
        set_task_header_st(o as *mut LeanObject);
        (*o).value = AtomicPtr::new(value);
        (*o).imp = core::ptr::null_mut();
        o as *mut LeanObject
    }

    pub fn new_task_manager(max_std_workers: usize) -> Arc<TaskManager> {
        Arc::new(TaskManager {
            inner: Mutex::new(TaskManagerInner {
                queues: core::array::from_fn(|_| VecDeque::new()),
                queues_size: 0,
                max_prio: 0,
                max_std_workers,
                std_workers: Vec::new(),
                total_std_workers: 0,
                idle_std_workers: 0,
                num_dedicated_workers: 0,
                shutting_down: false,
            }),
            queue_cv: Condvar::new(),
            task_finished_cv: Condvar::new(),
            dedicated_finished_cv: Condvar::new(),
        })
    }

    pub fn initiate_shutdown(tm: &TaskManager) {
        let std_workers = {
            let mut guard = tm.inner.lock().unwrap();
            if guard.shutting_down {
                return;
            }
            guard.shutting_down = true;
            std::mem::take(&mut guard.std_workers)
        };
        tm.queue_cv.notify_all();
        for worker in std_workers {
            worker.join().expect("lean worker thread panicked");
        }
        let guard = tm.inner.lock().unwrap();
        let _guard = tm
            .dedicated_finished_cv
            .wait_while(guard, |g| g.num_dedicated_workers > 0)
            .unwrap();
    }

    impl TaskManager {
        fn enqueue(self: &Arc<Self>, t: *mut LeanTaskObject) {
            let mut guard = self.inner.lock().unwrap();
            self.enqueue_core(&mut guard, t);
        }

        fn add_dep(self: &Arc<Self>, t1: *mut LeanTaskObject, t2: *mut LeanTaskObject) {
            if !unsafe { (*t1).value.load(Ordering::Acquire).is_null() } {
                self.enqueue(t2);
                return;
            }
            let mut guard = self.inner.lock().unwrap();
            if !unsafe { (*t1).value.load(Ordering::Acquire).is_null() } {
                self.enqueue_core(&mut guard, t2);
                return;
            }
            unsafe {
                let t2_imp = (*t2).imp as *mut LeanTaskImp;
                let t1_imp = (*t1).imp as *mut LeanTaskImp;
                (*t2_imp).m_next_dep = (*t1_imp).m_head_dep;
                (*t1_imp).m_head_dep = t2;
            }
        }

        fn wait_any(self: &Arc<Self>, task_list: *mut LeanObject) -> *mut LeanObject {
            if let Some(t) = Self::wait_any_check(task_list) {
                return t;
            }
            let mut guard = self.inner.lock().unwrap();
            loop {
                if let Some(t) = Self::wait_any_check(task_list) {
                    return t;
                }
                guard = self.task_finished_cv.wait(guard).unwrap();
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
        fn cancel_task(self: &Arc<Self>, t: *mut LeanTaskObject) {
            let _guard = self.inner.lock().unwrap();
            let imp = unsafe { (*t).imp as *mut LeanTaskImp };
            if !imp.is_null() {
                unsafe {
                    (*imp).m_canceled = true;
                }
            }
        }

        fn get_task_state(self: &Arc<Self>, t: *mut LeanTaskObject) -> u8 {
            let _guard = self.inner.lock().unwrap();
            let imp = unsafe { (*t).imp as *mut LeanTaskImp };
            if imp.is_null() {
                return 2; // finished
            }
            if unsafe { (*imp).m_closure.is_null() } {
                return 1; // running / promised
            }
            0 // waiting / queued
        }

        fn shutting_down(&self) -> bool {
            self.inner.lock().unwrap().shutting_down
        }

    }

    impl Drop for TaskManager {
        fn drop(&mut self) {
            if !self.inner.lock().unwrap().shutting_down {
                self.inner.lock().unwrap().shutting_down = true;
                self.queue_cv.notify_all();
            }
        }
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

    // ─── Task spawn ───────────────────────────────────────────────────────────

    pub unsafe fn lean_task_spawn_core(
        c: *mut LeanObject,
        prio: u32,
        keep_alive: bool,
    ) -> *mut LeanObject {
        if let Some(tm) = get_task_manager() {
            let t = alloc_running_task(c, prio, keep_alive);
            tm.enqueue(t);
            t as *mut LeanObject
        } else {
            lean_task_pure(lean_apply_1(c, lean_box(0)))
        }
    }

    // ─── Task map ─────────────────────────────────────────────────────────────

    unsafe fn task_map_fn(
        f: *mut LeanObject,
        t: *mut LeanObject,
        _w: *mut LeanObject,
    ) -> *mut LeanObject {
        // Actually we need the value, not imp:
        let v = (*(t as *mut LeanTaskObject)).value.load(Ordering::Relaxed);
        debug_assert!(!v.is_null());
        lean_inc(v);
        lean_dec_ref(t);
        lean_apply_1(f, v)
    }

    pub unsafe fn lean_task_map_core(
        f: *mut LeanObject,
        t: *mut LeanObject,
        prio: u32,
        sync: bool,
        keep_alive: bool,
    ) -> *mut LeanObject {
        let task = t as *mut LeanTaskObject;
        if let Some(tm) = get_task_manager() {
            if sync && !(*task).value.load(Ordering::Acquire).is_null() {
                return lean_task_pure(lean_apply_1(f, lean_task_get_own(t)));
            }
            let effective_prio = if sync { LEAN_SYNC_PRIO } else { prio };
            let closure = mk_closure_3_2(task_map_fn, f, t);
            let new_task = alloc_running_task(closure, effective_prio, keep_alive);
            tm.add_dep(task, new_task);
            new_task as *mut LeanObject
        } else {
            lean_task_pure(lean_apply_1(f, lean_task_get_own(t)))
        }
    }

    // ─── Task bind ────────────────────────────────────────────────────────────

    unsafe fn task_bind_fn2(t: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
        let v = (*(t as *mut LeanTaskObject)).value.load(Ordering::Relaxed);
        debug_assert!(!v.is_null());
        lean_inc(v);
        lean_dec_ref(t);
        v
    }

    unsafe fn task_bind_fn1(
        x: *mut LeanObject,
        f: *mut LeanObject,
        _w: *mut LeanObject,
    ) -> *mut LeanObject {
        let v = (*(x as *mut LeanTaskObject)).value.load(Ordering::Relaxed);
        debug_assert!(!v.is_null());
        lean_inc(v);
        lean_dec_ref(x);

        let new_task_obj = lean_apply_1(f, v);
        debug_assert!(!lean_is_scalar(new_task_obj) && (*new_task_obj).tag == LEAN_TASK_TAG);
        let new_task = new_task_obj as *mut LeanTaskObject;

        if !(*new_task).value.load(Ordering::Acquire).is_null() {
            let result = (*new_task).value.load(Ordering::Relaxed);
            lean_inc(result);
            lean_dec_ref(new_task_obj);
            return result;
        }

        // Suspend: store continuation in m_closure of the current task.
        let ct = current_task();
        debug_assert!(!ct.is_null());
        let ct_imp = (*ct).imp as *mut LeanTaskImp;
        debug_assert!((*ct_imp).m_closure.is_null());
        let continuation = mk_closure_2_1(task_bind_fn2, new_task_obj);
        lean_mark_mt(continuation);
        (*ct_imp).m_closure = continuation;
        core::ptr::null_mut()
    }

    pub unsafe fn lean_task_bind_core(
        x: *mut LeanObject,
        f: *mut LeanObject,
        prio: u32,
        sync: bool,
        keep_alive: bool,
    ) -> *mut LeanObject {
        let task = x as *mut LeanTaskObject;
        if let Some(tm) = get_task_manager() {
            if sync && !(*task).value.load(Ordering::Acquire).is_null() {
                return lean_apply_1(f, lean_task_get_own(x));
            }
            let effective_prio = if sync { LEAN_SYNC_PRIO } else { prio };
            let closure = mk_closure_3_2(task_bind_fn1, x, f);
            let new_task = alloc_running_task(closure, effective_prio, keep_alive);
            tm.add_dep(task, new_task);
            new_task as *mut LeanObject
        } else {
            lean_apply_1(f, lean_task_get_own(x))
        }
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
            .map(|tm| tm.shutting_down())
            .unwrap_or(false)
    }

    pub unsafe fn lean_io_cancel_core(t: *mut LeanObject) {
        let task = t as *mut LeanTaskObject;
        if !(*task).value.load(Ordering::Acquire).is_null() {
            return;
        }
        if let Some(tm) = get_task_manager() {
            tm.cancel_task(task);
        }
    }

    pub unsafe fn lean_io_get_task_state_core(t: *mut LeanObject) -> u8 {
        let task = t as *mut LeanTaskObject;
        if (*task).imp.is_null() {
            return 2; // finished
        }
        if let Some(tm) = get_task_manager() {
            tm.get_task_state(task)
        } else {
            2
        }
    }

    pub unsafe fn lean_io_wait_any_core(task_list: *mut LeanObject) -> *mut LeanObject {
        if let Some(tm) = get_task_manager() {
            tm.wait_any(task_list)
        } else {
            TaskManager::wait_any_check(task_list).unwrap_or(core::ptr::null_mut())
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
