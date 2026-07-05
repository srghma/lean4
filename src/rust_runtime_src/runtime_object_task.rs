/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the task-manager / promise section of src/runtime/object.cpp.
// Covers:
//   alloc_task_imp, free_task_imp, free_task
//   task_manager (priority queues, worker threads, dependency chains)
//   lean_task_spawn_core, lean_task_map_core, lean_task_bind_core, lean_task_get
//   lean_io_check_canceled_core, lean_io_cancel_core
//   lean_io_get_task_state_core, lean_io_wait_any_core
//   lean_promise_new, lean_promise_resolve  (C++ namespace → mangled names)
//   lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt
//   lean_init_task_manager, lean_init_task_manager_using, lean_finalize_task_manager
//   lean_runtime_deactivate_task, lean_runtime_deactivate_promise
//   lean_get_or_block

pub(crate) mod runtime_object_task_impl {
    use super::runtime_object_panic_impl::lean_internal_panic;
    use super::runtime_object_rc_impl::{lean_alloc_small_object, lean_free_small_object};
    use super::*;
    use core::sync::atomic::Ordering;
    use std::collections::VecDeque;
    use std::mem::MaybeUninit;
    use std::sync::{Arc, Condvar, Mutex, MutexGuard};
    use std::thread::JoinHandle;

    // ─── Constants ────────────────────────────────────────────────────────────

    const LEAN_MAX_PRIO: u32 = 8;
    const LEAN_SYNC_PRIO: u32 = u32::MAX;
    const LEAN_TASK_TAG: u8 = 252;
    const LEAN_PROMISE_TAG: u8 = 244;
    const LEAN_CLOSURE_TAG: u8 = 245;

    // ─── Helper: send raw pointer across threads ──────────────────────────────

    struct SendPtr<T>(*mut T);
    unsafe impl<T> Send for SendPtr<T> {}
    impl<T> SendPtr<T> {
        #[inline]
        fn get(&self) -> *mut T {
            self.0
        }
    }

    // ─── Helper: temporarily unlock a mutex guard ────────────────────────────

    macro_rules! with_mutex_unlocked {
        ($guard:ident, $mutex:expr, $body:block) => {{
            unsafe {
                let p: *mut _ = $guard;
                core::ptr::drop_in_place(p);
                let _result = $body;
                let new_guard = $mutex.lock().unwrap();
                core::ptr::write(p, core::mem::transmute(new_guard));
                _result
            }
        }};
    }

    // ─── Internal structure of a running task ─────────────────────────────────

    #[repr(C)]
    struct LeanTaskImp {
        m_closure: *mut LeanObject,
        m_head_dep: *mut LeanTaskObject,
        m_next_dep: *mut LeanTaskObject,
        m_prio: u32,
        m_canceled: bool,
        m_keep_alive: bool,
        m_deleted: bool,
    }

    // ─── Closure helpers ──────────────────────────────────────────────────────

    // Mirror of the lean.h inline lean_closure_object layout.
    #[repr(C)]
    struct LeanClosureLocal {
        header: LeanObject,
        fun: *mut c_void,
        arity: u16,
        num_fixed: u16,
        // 4 bytes of padding on 64-bit; zero-size array marks start of data
        data: [*mut LeanObject; 0],
    }

    #[inline(always)]
    unsafe fn local_alloc_closure(fun: *mut c_void, arity: u32, num_fixed: u32) -> *mut LeanObject {
        let byte_size = core::mem::size_of::<LeanClosureLocal>()
            + core::mem::size_of::<*mut LeanObject>() * num_fixed as usize;
        let obj = lean_alloc_object(byte_size) as *mut LeanClosureLocal;
        (*obj).header.rc = 1;
        (*obj).header.other = 0;
        (*obj).header.tag = LEAN_CLOSURE_TAG;
        #[cfg(not(lean_has_mimalloc))]
        {
            (*obj).header.cs_size = 0;
        }
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
    unsafe fn local_closure_arg_cptr(o: *mut LeanObject) -> *mut *mut LeanObject {
        (*(o as *mut LeanClosureLocal)).data.as_mut_ptr()
    }

    #[inline(always)]
    unsafe fn mk_closure_2_1(
        fun: unsafe extern "C" fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        let c = local_alloc_closure(fun as *mut c_void, 2, 1);
        local_closure_set(c, 0, a);
        c
    }

    #[inline(always)]
    unsafe fn mk_closure_3_2(
        fun: unsafe extern "C" fn(
            *mut LeanObject,
            *mut LeanObject,
            *mut LeanObject,
        ) -> *mut LeanObject,
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let c = local_alloc_closure(fun as *mut c_void, 3, 2);
        local_closure_set(c, 0, a1);
        local_closure_set(c, 1, a2);
        c
    }

    // ─── Option helpers ───────────────────────────────────────────────────────

    #[inline(always)]
    unsafe fn mk_option_none() -> *mut LeanObject {
        lean_box(0)
    }

    #[inline(always)]
    unsafe fn mk_option_some(v: *mut LeanObject) -> *mut LeanObject {
        let r = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(r, 0, v);
        r
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

    unsafe fn free_task_imp(imp: *mut LeanTaskImp) {
        lean_free_small_object(imp as *mut LeanObject);
    }

    unsafe fn free_task(t: *mut LeanTaskObject) {
        let imp = (*t).imp as *mut LeanTaskImp;
        if !imp.is_null() {
            free_task_imp(imp);
        }
        lean_free_small_object(t as *mut LeanObject);
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_task_pure(value: *mut LeanObject) -> *mut LeanObject {
        let o =
            lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
        set_task_header_st(o as *mut LeanObject);
        (*o).value = AtomicPtr::new(value);
        (*o).imp = core::ptr::null_mut();
        o as *mut LeanObject
    }

    // ─── Thread-local current task ────────────────────────────────────────────

    std::thread_local! {
        static G_CURRENT_TASK: core::cell::Cell<*mut LeanTaskObject> =
            const { core::cell::Cell::new(core::ptr::null_mut()) };
    }

    fn current_task() -> *mut LeanTaskObject {
        G_CURRENT_TASK.with(|c| c.get())
    }

    fn set_current_task(t: *mut LeanTaskObject) {
        G_CURRENT_TASK.with(|c| c.set(t));
    }

    struct ScopedCurrentTask {
        prev: *mut LeanTaskObject,
    }
    impl ScopedCurrentTask {
        fn new(t: *mut LeanTaskObject) -> Self {
            let prev = current_task();
            set_current_task(t);
            ScopedCurrentTask { prev }
        }
    }
    impl Drop for ScopedCurrentTask {
        fn drop(&mut self) {
            set_current_task(self.prev);
        }
    }

    // ─── Task manager internals ───────────────────────────────────────────────

    struct TaskManagerInner {
        queues: [VecDeque<*mut LeanTaskObject>; (LEAN_MAX_PRIO + 1) as usize],
        queues_size: usize,
        max_prio: usize,
        max_std_workers: usize,
        std_workers: Vec<JoinHandle<()>>,
        total_std_workers: usize,
        idle_std_workers: usize,
        num_dedicated_workers: usize,
        shutting_down: bool,
    }

    // SAFETY: task object pointers are shared under the mutex.
    unsafe impl Send for TaskManagerInner {}

    struct TaskManager {
        inner: Mutex<TaskManagerInner>,
        queue_cv: Condvar,
        task_finished_cv: Condvar,
        dedicated_finished_cv: Condvar,
    }

    unsafe impl Send for TaskManager {}
    unsafe impl Sync for TaskManager {}

    impl TaskManager {
        fn new(max_std_workers: usize) -> Arc<Self> {
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

        fn enqueue(self: &Arc<Self>, t: *mut LeanTaskObject) {
            let mut guard = self.inner.lock().unwrap();
            self.enqueue_core(&mut guard, t);
        }

        fn enqueue_core(
            self: &Arc<Self>,
            guard: &mut MutexGuard<'_, TaskManagerInner>,
            t: *mut LeanTaskObject,
        ) {
            let prio = unsafe { (*((*t).imp as *mut LeanTaskImp)).m_prio };

            if prio == LEAN_SYNC_PRIO {
                self.run_task_locked(guard, t);
                return;
            }
            if prio > LEAN_MAX_PRIO {
                self.spawn_dedicated_worker(guard, t);
                return;
            }
            let prio_idx = prio as usize;
            if prio_idx > guard.max_prio {
                guard.max_prio = prio_idx;
            }
            guard.queues[prio_idx].push_back(t);
            guard.queues_size += 1;

            if guard.idle_std_workers == 0 && guard.total_std_workers < guard.max_std_workers {
                self.spawn_worker(guard);
            } else {
                self.queue_cv.notify_one();
            }
        }

        fn dequeue(guard: &mut TaskManagerInner) -> *mut LeanTaskObject {
            debug_assert!(guard.queues_size > 0);
            let q = &mut guard.queues[guard.max_prio];
            let t = q.pop_front().unwrap();
            guard.queues_size -= 1;
            if q.is_empty() {
                while guard.max_prio > 0 {
                    guard.max_prio -= 1;
                    if !guard.queues[guard.max_prio].is_empty() {
                        break;
                    }
                }
            }
            t
        }

        fn spawn_worker(self: &Arc<Self>, guard: &mut MutexGuard<'_, TaskManagerInner>) {
            if guard.shutting_down {
                return;
            }
            guard.total_std_workers += 1;
            let tm = Arc::clone(self);
            let handle = spawn_lean_worker(move || {
                unsafe {
                    save_stack_info(false);
                }
                let mut guard = tm.inner.lock().unwrap();
                guard.idle_std_workers += 1;
                loop {
                    if guard.queues_size == 0 {
                        if guard.shutting_down {
                            break;
                        }
                        guard = tm.queue_cv.wait(guard).unwrap();
                        continue;
                    }
                    // Throttle if over max (but not during shutdown).
                    if !guard.shutting_down
                        && guard.total_std_workers - guard.idle_std_workers >= guard.max_std_workers
                    {
                        guard = tm.queue_cv.wait(guard).unwrap();
                        continue;
                    }
                    let t = TaskManager::dequeue(&mut guard);
                    guard.idle_std_workers -= 1;
                    tm.run_task_locked(&mut guard, t);
                    guard.idle_std_workers += 1;
                    reset_heartbeat();
                }
                guard.idle_std_workers -= 1;
                guard.total_std_workers -= 1;
            });
            guard.std_workers.push(handle);
        }

        fn spawn_dedicated_worker(
            self: &Arc<Self>,
            guard: &mut MutexGuard<'_, TaskManagerInner>,
            t: *mut LeanTaskObject,
        ) {
            guard.num_dedicated_workers += 1;
            let tm = Arc::clone(self);
            let t_send = SendPtr(t);
            spawn_lean_worker(move || {
                unsafe {
                    save_stack_info(false);
                }
                let mut guard = tm.inner.lock().unwrap();
                tm.run_task_locked(&mut guard, t_send.get());
                guard.num_dedicated_workers -= 1;
                tm.dedicated_finished_cv.notify_all();
            });
        }

        fn run_task_locked(
            self: &Arc<Self>,
            guard: &mut MutexGuard<'_, TaskManagerInner>,
            t: *mut LeanTaskObject,
        ) {
            let imp = unsafe { (*t).imp as *mut LeanTaskImp };
            debug_assert!(!imp.is_null());

            if unsafe { (*imp).m_deleted } {
                unsafe {
                    free_task(t);
                }
                return;
            }

            reset_heartbeat();

            let closure = unsafe {
                let c = (*imp).m_closure;
                (*imp).m_closure = core::ptr::null_mut();
                c
            };

            let result = with_mutex_unlocked!(guard, self.inner, {
                let _scope = ScopedCurrentTask::new(t);
                let result = lean_apply_1(closure, lean_box(0));
                if !result.is_null() {
                    let imp2 = (*t).imp as *mut LeanTaskImp;
                    if (*imp2).m_keep_alive {
                        lean_dec_ref(t as *mut LeanObject);
                    }
                }
                result
            });

            let imp3 = unsafe { (*t).imp as *mut LeanTaskImp };
            debug_assert!(!imp3.is_null());

            if unsafe { (*imp3).m_deleted } {
                with_mutex_unlocked!(guard, self.inner, {
                    if !result.is_null() {
                        lean_dec(result);
                    }
                    free_task(t);
                });
            } else if !result.is_null() {
                self.resolve_core(guard, t, result);
            } else {
                // Bind task suspended — re-registered as dep of a nested task.
                // The closure pointer was updated by task_bind_fn1.
                let new_closure = unsafe { (*imp3).m_closure };
                with_mutex_unlocked!(guard, self.inner, {
                    let nested_ptr =
                        local_closure_arg_cptr(new_closure) as *mut *mut LeanTaskObject;
                    let nested = *nested_ptr;
                    self.add_dep_raw(nested, t);
                });
            }
        }

        fn resolve_core(
            self: &Arc<Self>,
            guard: &mut MutexGuard<'_, TaskManagerInner>,
            t: *mut LeanTaskObject,
            v: *mut LeanObject,
        ) {
            unsafe {
                lean_mark_mt(v);
            }
            unsafe {
                (*t).value.store(v, Ordering::Release);
            }
            let imp = unsafe {
                let imp = (*t).imp as *mut LeanTaskImp;
                (*t).imp = core::ptr::null_mut();
                imp
            };
            self.handle_finished(guard, t, imp);
            unsafe {
                free_task_imp(imp);
            }
            self.task_finished_cv.notify_all();
        }

        fn handle_finished(
            self: &Arc<Self>,
            guard: &mut MutexGuard<'_, TaskManagerInner>,
            _t: *mut LeanTaskObject,
            imp: *mut LeanTaskImp,
        ) {
            let canceled = unsafe { (*imp).m_canceled };
            let mut it = unsafe { (*imp).m_head_dep };
            unsafe {
                (*imp).m_head_dep = core::ptr::null_mut();
            }
            while !it.is_null() {
                let it_imp = unsafe { (*it).imp as *mut LeanTaskImp };
                if canceled {
                    unsafe {
                        (*it_imp).m_canceled = true;
                    }
                }
                let next = unsafe { (*it_imp).m_next_dep };
                unsafe {
                    (*it_imp).m_next_dep = core::ptr::null_mut();
                }
                if unsafe { (*it_imp).m_deleted } {
                    unsafe {
                        free_task(it);
                    }
                } else {
                    self.enqueue_core(guard, it);
                }
                it = next;
            }
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

        unsafe fn add_dep_raw(self: &Arc<Self>, t1: *mut LeanTaskObject, t2: *mut LeanTaskObject) {
            let mut guard = self.inner.lock().unwrap();
            if !(*t1).value.load(Ordering::Acquire).is_null() {
                self.enqueue_core(&mut guard, t2);
                return;
            }
            let t2_imp = (*t2).imp as *mut LeanTaskImp;
            let t1_imp = (*t1).imp as *mut LeanTaskImp;
            (*t2_imp).m_next_dep = (*t1_imp).m_head_dep;
            (*t1_imp).m_head_dep = t2;
        }

        fn wait_for(self: &Arc<Self>, t: *mut LeanTaskObject) {
            if !unsafe { (*t).value.load(Ordering::Acquire).is_null() } {
                return;
            }
            let mut guard = self.inner.lock().unwrap();
            if !unsafe { (*t).value.load(Ordering::Acquire).is_null() } {
                return;
            }

            let ct = current_task();
            let in_pool = !ct.is_null()
                && unsafe { (*((*ct).imp as *mut LeanTaskImp)).m_prio <= LEAN_MAX_PRIO };

            if !ct.is_null() {
                let ct_imp = unsafe { (*ct).imp as *mut LeanTaskImp };
                if unsafe { (*ct_imp).m_prio == LEAN_SYNC_PRIO } {
                    unsafe {
                        lean_panic(
                            c"`Task.get` called from a `(sync := true)` task".as_ptr(),
                            false,
                        );
                    }
                }
            }

            if in_pool {
                guard.max_std_workers += 1;
                if guard.idle_std_workers == 0 && guard.total_std_workers < guard.max_std_workers {
                    self.spawn_worker(&mut guard);
                } else {
                    self.queue_cv.notify_one();
                }
            }

            guard = self
                .task_finished_cv
                .wait_while(guard, |_| unsafe {
                    (*t).value.load(Ordering::Acquire).is_null()
                })
                .unwrap();

            if in_pool {
                guard.max_std_workers -= 1;
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

        fn resolve(self: &Arc<Self>, t: *mut LeanTaskObject, v: *mut LeanObject) {
            if !unsafe { (*t).value.load(Ordering::Acquire).is_null() } {
                unsafe {
                    lean_dec(v);
                }
                return;
            }
            let mut guard = self.inner.lock().unwrap();
            if !unsafe { (*t).value.load(Ordering::Acquire).is_null() } {
                drop(guard);
                unsafe {
                    lean_dec(v);
                }
                return;
            }
            self.resolve_core(&mut guard, t, v);
        }

        fn deactivate_task_obj(self: &Arc<Self>, t: *mut LeanTaskObject) {
            let mut guard = self.inner.lock().unwrap();
            let v = unsafe { (*t).value.load(Ordering::Acquire) };
            if !v.is_null() {
                debug_assert!(unsafe { (*t).imp.is_null() });
                drop(guard);
                unsafe {
                    lean_dec(v);
                }
                unsafe {
                    free_task(t);
                }
                return;
            }
            debug_assert!(!unsafe { (*t).imp.is_null() });
            self.deactivate_task_core(&mut guard, t);
        }

        fn deactivate_task_core(
            self: &Arc<Self>,
            guard: &mut MutexGuard<'_, TaskManagerInner>,
            t: *mut LeanTaskObject,
        ) {
            let imp = unsafe { (*t).imp as *mut LeanTaskImp };
            let closure = unsafe { (*imp).m_closure };
            let mut it = unsafe { (*imp).m_head_dep };
            unsafe {
                (*imp).m_closure = core::ptr::null_mut();
                (*imp).m_head_dep = core::ptr::null_mut();
                (*imp).m_canceled = true;
                (*imp).m_deleted = true;
            }
            with_mutex_unlocked!(guard, self.inner, {
                while !it.is_null() {
                    let it_imp = (*it).imp as *mut LeanTaskImp;
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

        fn initiate_shutdown(&self) {
            let std_workers = {
                let mut guard = self.inner.lock().unwrap();
                if guard.shutting_down {
                    return;
                }
                guard.shutting_down = true;
                std::mem::take(&mut guard.std_workers)
            };
            self.queue_cv.notify_all();
            for worker in std_workers {
                worker.join().expect("lean worker thread panicked");
            }
            let guard = self.inner.lock().unwrap();
            let _guard = self
                .dedicated_finished_cv
                .wait_while(guard, |g| g.num_dedicated_workers > 0)
                .unwrap();
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

    // ─── Global task manager ──────────────────────────────────────────────────

    static G_TASK_MANAGER: std::sync::OnceLock<std::sync::Mutex<Option<Arc<TaskManager>>>> =
        std::sync::OnceLock::new();

    fn task_manager_cell() -> &'static std::sync::Mutex<Option<Arc<TaskManager>>> {
        G_TASK_MANAGER.get_or_init(|| std::sync::Mutex::new(None))
    }

    fn get_task_manager() -> Option<Arc<TaskManager>> {
        task_manager_cell().lock().unwrap().clone()
    }

    fn set_task_manager(tm: Option<Arc<TaskManager>>) {
        *task_manager_cell().lock().unwrap() = tm;
    }

    // ─── Worker thread spawning ───────────────────────────────────────────────

    extern "C" {
        fn lean_initialize_thread();
        fn lean_finalize_thread();
        fn lean_panic(msg: *const core::ffi::c_char, force_stderr: bool);
    }

    fn spawn_lean_worker<F: FnOnce() + Send + 'static>(f: F) -> JoinHandle<()> {
        #[cfg(target_pointer_width = "64")]
        const STACK_SIZE: usize = 1024 * 1024 * 1024; // 1 GB
        #[cfg(not(target_pointer_width = "64"))]
        const STACK_SIZE: usize = 8 * 1024 * 1024; // 8 MB

        std::thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(move || unsafe {
                let mut guard = MaybeUninit::<StackGuard>::uninit();
                stack_guard_ctor_complete(guard.as_mut_ptr());
                lean_initialize_thread();
                f();
                lean_finalize_thread();
                stack_guard_dtor_complete(guard.as_mut_ptr());
            })
            .expect("failed to spawn lean worker thread")
    }

    // ─── Init / finalize task manager ────────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_init_task_manager_using(num_workers: u32) {
        debug_assert!(get_task_manager().is_none());
        #[cfg(lean_multi_thread)]
        if num_workers > 0 {
            set_task_manager(Some(TaskManager::new(num_workers as usize)));
        }
        #[cfg(not(lean_multi_thread))]
        let _ = num_workers;
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_init_task_manager() {
        lean_init_task_manager_using(unsafe { lean_runtime_get_lean_num_threads() });
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_finalize_task_manager() {
        if let Some(tm) = get_task_manager() {
            tm.initiate_shutdown();
        }
        set_task_manager(None);
    }

    // ─── Task spawn ───────────────────────────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_task_spawn_core(
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

    unsafe extern "C" fn task_map_fn(
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_task_map_core(
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

    unsafe extern "C" fn task_bind_fn2(t: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
        let v = (*(t as *mut LeanTaskObject)).value.load(Ordering::Relaxed);
        debug_assert!(!v.is_null());
        lean_inc(v);
        lean_dec_ref(t);
        v
    }

    unsafe extern "C" fn task_bind_fn1(
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_task_bind_core(
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

    // ─── Task get ─────────────────────────────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_task_get(t: *mut LeanObject) -> *mut LeanObject {
        let task = t as *mut LeanTaskObject;
        let v = (*task).value.load(Ordering::Acquire);
        if !v.is_null() {
            return v;
        }
        if let Some(tm) = get_task_manager() {
            tm.wait_for(task);
        }
        let v2 = (*task).value.load(Ordering::Acquire);
        debug_assert!(!v2.is_null());
        v2
    }

    unsafe fn lean_task_get_own(t: *mut LeanObject) -> *mut LeanObject {
        let v = lean_task_get(t);
        lean_inc(v);
        lean_dec_ref(t);
        v
    }

    // ─── IO task helpers ──────────────────────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_io_check_canceled_core() -> bool {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_cancel_core(t: *mut LeanObject) {
        let task = t as *mut LeanTaskObject;
        if !(*task).value.load(Ordering::Acquire).is_null() {
            return;
        }
        if let Some(tm) = get_task_manager() {
            tm.cancel_task(task);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_get_task_state_core(t: *mut LeanObject) -> u8 {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_wait_any_core(task_list: *mut LeanObject) -> *mut LeanObject {
        if let Some(tm) = get_task_manager() {
            tm.wait_any(task_list)
        } else {
            TaskManager::wait_any_check(task_list).unwrap_or(core::ptr::null_mut())
        }
    }

    // ─── Deactivate task / promise (called from runtime_object_rc.rs) ─────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_runtime_deactivate_task(t: *mut LeanTaskObject) {
        if let Some(tm) = get_task_manager() {
            tm.deactivate_task_obj(t);
        } else {
            let v = (*t).value.load(Ordering::Acquire);
            debug_assert!(!v.is_null());
            lean_dec(v);
            free_task(t);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_runtime_deactivate_promise(promise: *mut LeanPromiseObject) {
        if let Some(tm) = get_task_manager() {
            let none = mk_option_none();
            tm.resolve((*promise).result as *mut LeanTaskObject, none);
            lean_dec_ref((*promise).result);
        }
        lean_free_small_object(promise as *mut LeanObject);
    }

    // ─── Promise new / resolve ────────────────────────────────────────────────

    // lean::lean_promise_new (C++ namespace → mangled name)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean16lean_promise_newEv"
    )]
    pub unsafe extern "C" fn lean_promise_new_impl() -> *mut LeanObject {
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
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean20lean_promise_resolveEP11lean_objectS1_"
    )]
    pub unsafe extern "C" fn lean_promise_resolve_impl(
        value: *mut LeanObject,
        promise: *mut LeanObject,
    ) {
        let p = promise as *mut LeanPromiseObject;
        if let Some(tm) = get_task_manager() {
            let some_value = mk_option_some(value);
            tm.resolve((*p).result as *mut LeanTaskObject, some_value);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_promise_new() -> *mut LeanObject {
        lean_promise_new_impl()
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_promise_resolve(
        value: *mut LeanObject,
        promise: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_promise_resolve_impl(value, promise);
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_promise_result_opt(
        promise: *mut LeanObject,
    ) -> *mut LeanObject {
        let p = promise as *mut LeanPromiseObject;
        let t = (*p).result;
        lean_inc_ref(t);
        t
    }

    // ─── lean_get_or_block (IO.getOrBlock) ────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_get_or_block(opt: *mut LeanObject) -> *mut LeanObject {
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
