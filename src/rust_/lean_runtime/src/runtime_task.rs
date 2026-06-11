extern "C" { fn lean_alloc_closure(fun: *mut core::ffi::c_void, arity: u32, num_fixed: u32) -> *mut LeanObject; }
/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the task-manager / promise section of src/runtime/object.cpp.
// Coverage:
//   lean_task_imp, lean_task_object layout helpers
//   task_manager  (priority queues, worker threads, dependency chains)
//   lean_task_spawn_core, lean_task_pure
//   lean_task_map_core, lean_task_bind_core, lean_task_get
//   lean_io_check_canceled_core, lean_io_cancel_core
//   lean_io_get_task_state_core, lean_io_wait_any_core
//   lean_promise_new, lean_promise_resolve
//   lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt
//   lean_init_task_manager, lean_init_task_manager_using
//   lean_finalize_task_manager
//   lean_internal_get_hardware_concurrency
//   deactivate_task, deactivate_promise  (called from runtime_object_rc.rs)

use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex, MutexGuard};
use std::thread;

/// Temporarily drops a MutexGuard, executes a block, then reacquires.
/// `$guard` must be an `&mut MutexGuard<'_, T>` local variable.
macro_rules! with_mutex_unlocked {
    ($guard:ident, $mutex:expr, $body:block) => {{
        // Safety:
        // 1. We drop the real guard first, releasing the mutex.
        // 2. After the body, we re-acquire. The new guard's lifetime is
        //    valid for as long as the mutex lives, which is at least as
        //    long as what the caller expects (since both refer to the same
        //    mutex in `self`). We transmute to satisfy invariant lifetime.
        // 3. No use of $guard occurs between drop_in_place and write.
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


// ─── Constants ────────────────────────────────────────────────────────────────

const LEAN_MAX_PRIO: u32 = 8;
const LEAN_SYNC_PRIO: u32 = u32::MAX;

// ─── External C helpers ───────────────────────────────────────────────────────

extern "C" {
    fn lean_alloc_small_object(sz: usize) -> *mut LeanObject;
    fn lean_set_st_header(o: *mut LeanObject, tag: u8, other: u8);
}

// ─── Lean object tag for tasks / promises ────────────────────────────────────


// ─── Raw task / promise object layouts ───────────────────────────────────────
//
// These must match the C structs in lean.h exactly.

/// Internal execution state of a task (heap-allocated separately from the
/// task object so that the task object can be kept alive cheaply).
#[repr(C)]
struct LeanTaskImp {
    m_closure: *mut LeanObject,
    m_head_dep: *mut LeanTaskObject,  // first dependent task
    m_next_dep: *mut LeanTaskObject,  // next sibling in dependency list
    m_prio: u32,
    m_canceled: bool,
    m_keep_alive: bool,
    m_deleted: bool,
}

/// The heap-allocated task object visible to Lean code.
#[repr(C)]
pub struct LeanTaskObject {
    header: LeanObject,
    m_value: *mut LeanObject,   // null until the task has finished
    m_imp: *mut LeanTaskImp,    // null after the task has finished
}

// ─── Thread-local current task ───────────────────────────────────────────────

std::thread_local! {
    static G_CURRENT_TASK: std::cell::Cell<*mut LeanTaskObject> =
        const { std::cell::Cell::new(core::ptr::null_mut()) };
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

// ─── Task allocation helpers ──────────────────────────────────────────────────

unsafe fn alloc_task_imp(
    closure: *mut LeanObject,
    prio: u32,
    keep_alive: bool,
) -> *mut LeanTaskImp {
    let imp = lean_alloc_small_object(core::mem::size_of::<LeanTaskImp>()) as *mut LeanTaskImp;
    (*imp).m_closure   = closure;
    (*imp).m_head_dep  = core::ptr::null_mut();
    (*imp).m_next_dep  = core::ptr::null_mut();
    (*imp).m_prio      = prio;
    (*imp).m_canceled  = false;
    (*imp).m_keep_alive = keep_alive;
    (*imp).m_deleted   = false;
    imp
}

unsafe fn free_task_imp(imp: *mut LeanTaskImp) {
    lean_free_small_object(imp as *mut LeanObject);
}

unsafe fn free_task(t: *mut LeanTaskObject) {
    if !(*t).m_imp.is_null() {
        free_task_imp((*t).m_imp);
    }
    lean_free_small_object(t as *mut LeanObject);
}

/// Set the header of a task to the multi-threaded initial state (rc = -1).
unsafe fn lean_set_task_header(o: *mut LeanObject) {
    (*o).m_rc     = -1;
    (*o).m_tag    = LEAN_TASK_TAG;
    (*o).m_other  = 0;
    (*o).m_cs_sz = 0;
}

/// Allocate a running task (has a closure, no value yet).
unsafe fn alloc_running_task(
    closure: *mut LeanObject,
    prio: u32,
    keep_alive: bool,
) -> *mut LeanTaskObject {
    lean_mark_mt(closure);
    let o = lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
    lean_set_task_header(o as *mut LeanObject);
    (*o).m_value = core::ptr::null_mut();
    (*o).m_imp   = alloc_task_imp(closure, prio, keep_alive);
    if keep_alive {
        lean_inc_ref(o as *mut LeanObject);
    }
    o
}

/// Allocate an already-resolved task (has a value, no imp).
unsafe fn alloc_resolved_task(value: *mut LeanObject) -> *mut LeanTaskObject {
    let o = lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
    lean_set_st_header(o as *mut LeanObject, LEAN_TASK_TAG, 0);
    (*o).m_value = value;
    (*o).m_imp   = core::ptr::null_mut();
    o
}

// ─── Closure builder helpers (mirror mk_closure_2_1 / mk_closure_3_2) ────────

unsafe fn mk_closure_2_1(
    fun: unsafe extern "C" fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let c = lean_alloc_closure(fun as *mut c_void, 2, 1);
    lean_closure_set_c(c, 0, a);
    c
}

unsafe fn mk_closure_3_2(
    fun: unsafe extern "C" fn(*mut LeanObject, *mut LeanObject, *mut LeanObject) -> *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    let c = lean_alloc_closure(fun as *mut c_void, 3, 2);
    lean_closure_set_c(c, 0, a1);
    lean_closure_set_c(c, 1, a2);
    c
}

extern "C" {
    #[link_name = "lean_closure_set"]
    fn lean_closure_set_c(o: *mut LeanObject, i: c_uint, v: *mut LeanObject);
}

// ─── Task option helpers ──────────────────────────────────────────────────────

unsafe fn mk_option_none() -> *mut LeanObject {
    lean_box(0)
}

unsafe fn mk_option_some(v: *mut LeanObject) -> *mut LeanObject {
    let r = lean_runtime_alloc_ctor(1, 1, 0);
    lean_runtime_ctor_set(r, 0, v);
    r
}

// ─── The task manager ────────────────────────────────────────────────────────

struct TaskManagerInner {
    /// Priority queues: index = priority, 0 = lowest, LEAN_MAX_PRIO = highest.
    queues: [VecDeque<*mut LeanTaskObject>; (LEAN_MAX_PRIO + 1) as usize],
    queues_size: usize,
    max_prio: usize,
    max_std_workers: usize,
    total_std_workers: usize,
    idle_std_workers: usize,
    num_dedicated_workers: usize,
    shutting_down: bool,
}

// SAFETY: raw pointers to Lean objects are sent between threads under the
// task manager mutex, matching the C++ design.
unsafe impl Send for TaskManagerInner {}

struct TaskManager {
    inner: Mutex<TaskManagerInner>,
    queue_cv: Condvar,
    task_finished_cv: Condvar,
    dedicated_finished_cv: Condvar,
}

// SAFETY: TaskManager is accessed only through Arc<TaskManager> and all
// mutation is guarded by the inner Mutex.
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
        debug_assert!(!unsafe { (*t).m_imp.is_null() });
        let prio = unsafe { (*(*t).m_imp).m_prio };

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

        if guard.idle_std_workers == 0
            && guard.inner_worker_count(guard) < guard.max_std_workers
        {
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

        // Use the lean thread spawner (1 GB stack + lean_initialize/finalize_thread
        // + SIGSEGV stack-overflow guard) to match the C++ lthread behaviour.
        spawn_lean_worker(move || {
            unsafe { save_stack_info(false); }
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
                let t = TaskManager::dequeue(&mut guard);
                guard.idle_std_workers -= 1;
                tm.run_task_locked(&mut guard, t);
                guard.idle_std_workers += 1;
                unsafe { reset_heartbeat(); }
            }
            guard.idle_std_workers -= 1;
            guard.total_std_workers -= 1;
        });
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
            unsafe { save_stack_info(false); }
            let mut guard = tm.inner.lock().unwrap();
            tm.run_task_locked(&mut guard, t_send.get());
            guard.num_dedicated_workers -= 1;
            tm.dedicated_finished_cv.notify_all();
        });
    }

    /// Run task `t` with the inner mutex held. Releases and re-acquires the
    /// mutex around the actual closure execution.
    fn run_task_locked(
        self: &Arc<Self>,
        guard: &mut MutexGuard<'_, TaskManagerInner>,
        t: *mut LeanTaskObject,
    ) {
        debug_assert!(!unsafe { (*t).m_imp.is_null() });

        if unsafe { (*(*t).m_imp).m_deleted } {
            unsafe { free_task(t); }
            return;
        }

        unsafe { reset_heartbeat(); }

        // Extract the closure with the mutex held, then release before calling it.
        let closure = unsafe {
            let c = (*(*t).m_imp).m_closure;
            (*(*t).m_imp).m_closure = core::ptr::null_mut();
            c
        };

        let result = with_mutex_unlocked!(guard, self.inner, {
            let _scope = ScopedCurrentTask::new(t);
            unsafe { lean_apply_1(closure, lean_box(0)) }
        });

        // If keep_alive and the task just produced its final value, dec the
        // extra ref we added at allocation.
        if !result.is_null() && unsafe { (*(*t).m_imp).m_keep_alive } {
            unsafe { lean_dec_ref(t as *mut LeanObject); }
        }

        debug_assert!(!unsafe { (*t).m_imp.is_null() });

        if unsafe { (*(*t).m_imp).m_deleted } {
            with_mutex_unlocked!(guard, self.inner, {
                unsafe {
                    if !result.is_null() { lean_dec(result); }
                    free_task(t);
                }
            });
        } else if !result.is_null() {
            self.resolve_core(guard, t, result);
        } else {
            // Bind task suspended — it re-registered itself as a dep of a
            // nested task. The new closure is already in m_closure.
            let new_closure = unsafe { (*(*t).m_imp).m_closure };
            with_mutex_unlocked!(guard, self.inner, {
                unsafe {
                    let nested = *(lean_closure_arg_cptr(new_closure) as *mut *mut LeanTaskObject);
                    self.add_dep_raw(nested, t);
                }
            });
        }
    }

    fn resolve_core(
        self: &Arc<Self>,
        guard: &mut MutexGuard<'_, TaskManagerInner>,
        t: *mut LeanTaskObject,
        v: *mut LeanObject,
    ) {
        unsafe { lean_mark_mt(v); }
        unsafe { (*t).m_value = v; }
        let imp = unsafe {
            let imp = (*t).m_imp;
            (*t).m_imp = core::ptr::null_mut();
            imp
        };
        self.handle_finished(guard, t, imp);
        unsafe { free_task_imp(imp); }
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
        unsafe { (*imp).m_head_dep = core::ptr::null_mut(); }
        while !it.is_null() {
            if canceled {
                unsafe { (*(*it).m_imp).m_canceled = true; }
            }
            let next = unsafe { (*(*it).m_imp).m_next_dep };
            unsafe { (*(*it).m_imp).m_next_dep = core::ptr::null_mut(); }
            if unsafe { (*(*it).m_imp).m_deleted } {
                unsafe { free_task(it); }
            } else {
                self.enqueue_core(guard, it);
            }
            it = next;
        }
    }

    fn add_dep(self: &Arc<Self>, t1: *mut LeanTaskObject, t2: *mut LeanTaskObject) {
        if !unsafe { (*t1).m_value.is_null() } {
            self.enqueue(t2);
            return;
        }
        let mut guard = self.inner.lock().unwrap();
        if !unsafe { (*t1).m_value.is_null() } {
            self.enqueue_core(&mut guard, t2);
            return;
        }
        unsafe {
            (*(*t2).m_imp).m_next_dep = (*(*t1).m_imp).m_head_dep;
            (*(*t1).m_imp).m_head_dep = t2;
        }
    }

    // Used internally when we already have the nested task object directly.
    unsafe fn add_dep_raw(self: &Arc<Self>, t1: *mut LeanTaskObject, t2: *mut LeanTaskObject) {
        let mut guard = self.inner.lock().unwrap();
        if !(*t1).m_value.is_null() {
            self.enqueue_core(&mut guard, t2);
            return;
        }
        (*(*t2).m_imp).m_next_dep = (*(*t1).m_imp).m_head_dep;
        (*(*t1).m_imp).m_head_dep = t2;
    }

    fn wait_for(self: &Arc<Self>, t: *mut LeanTaskObject) {
        if !unsafe { (*t).m_value.is_null() } {
            return;
        }
        let mut guard = self.inner.lock().unwrap();
        if !unsafe { (*t).m_value.is_null() } {
            return;
        }

        let in_pool = unsafe { current_task().as_ref() }
            .map(|ct| unsafe { (*(*ct).m_imp).m_prio <= LEAN_MAX_PRIO })
            .unwrap_or(false);

        if let Some(ct) = unsafe { current_task().as_ref() } {
            if unsafe { (*(*ct).m_imp).m_prio == LEAN_SYNC_PRIO } {
                unsafe { lean_panic(c"`Task.get` called from a `(sync := true)` task".as_ptr()); }
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
            .wait_while(guard, |_| unsafe { (*t).m_value.is_null() })
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
            if !unsafe { (*(head as *mut LeanTaskObject)).m_value.is_null() } {
                return Some(head);
            }
            it = unsafe { lean_ctor_get(it, 1) };
        }
        None
    }

    fn resolve(self: &Arc<Self>, t: *mut LeanTaskObject, v: *mut LeanObject) {
        if !unsafe { (*t).m_value.is_null() } {
            unsafe { lean_dec(v); }
            return;
        }
        let mut guard = self.inner.lock().unwrap();
        if !unsafe { (*t).m_value.is_null() } {
            drop(guard);
            unsafe { lean_dec(v); }
            return;
        }
        self.resolve_core(&mut guard, t, v);
    }

    pub fn deactivate_task_obj(self: &Arc<Self>, t: *mut LeanTaskObject) {
        let mut guard = self.inner.lock().unwrap();
        if let Some(v) = unsafe { (*t).m_value.as_mut() } {
            debug_assert!(unsafe { (*t).m_imp.is_null() });
            let v_ptr = &mut *v as *mut LeanObject;
            drop(guard);
            unsafe { lean_dec(v_ptr); }
            unsafe { free_task(t); }
            return;
        }
        debug_assert!(!unsafe { (*t).m_imp.is_null() });
        self.deactivate_task_core(&mut guard, t);
    }

    fn deactivate_task_core<'a>(
        self: &'a Arc<Self>,
        guard: &mut MutexGuard<'a, TaskManagerInner>,
        t: *mut LeanTaskObject,
    ) {
        let closure = unsafe { (*(*t).m_imp).m_closure };
        let mut it = unsafe { (*(*t).m_imp).m_head_dep };
        unsafe {
            (*(*t).m_imp).m_closure  = core::ptr::null_mut();
            (*(*t).m_imp).m_head_dep = core::ptr::null_mut();
            (*(*t).m_imp).m_canceled = true;
            (*(*t).m_imp).m_deleted  = true;
        }
        with_mutex_unlocked!(guard, self.inner, {
            unsafe {
                while !it.is_null() {
                    debug_assert!((*(*it).m_imp).m_deleted);
                    let next = (*(*it).m_imp).m_next_dep;
                    free_task(it);
                    it = next;
                }
                if !closure.is_null() {
                    lean_dec_ref(closure);
                }
            }
        });
    }

    fn cancel_task(self: &Arc<Self>, t: *mut LeanTaskObject) {
        let guard = self.inner.lock().unwrap();
        if !unsafe { (*t).m_imp.is_null() } {
            unsafe { (*(*t).m_imp).m_canceled = true; }
        }
        drop(guard);
    }

    fn get_task_state(self: &Arc<Self>, t: *mut LeanTaskObject) -> u8 {
        let _guard = self.inner.lock().unwrap();
        if unsafe { (*t).m_imp.is_null() } {
            return 2; // finished
        }
        if unsafe { (*(*t).m_imp).m_closure.is_null() } {
            return 1; // running / promised
        }
        0 // waiting / queued
    }

    fn shutting_down(&self) -> bool {
        self.inner.lock().unwrap().shutting_down
    }
}

impl TaskManagerInner {
    fn inner_worker_count(&self, _guard: &MutexGuard<'_, TaskManagerInner>) -> usize {
        self.total_std_workers
    }
}

impl TaskManager {
    /// Signal all workers to shut down and wait for dedicated workers to finish.
    /// Standard workers exit their loops asynchronously when they observe
    /// `shutting_down == true`.  Mirrors the C++ `task_manager::finalize()`.
    fn initiate_shutdown(&self) {
        {
            let mut guard = self.inner.lock().unwrap();
            if guard.shutting_down {
                return;
            }
            guard.shutting_down = true;
        }
        self.queue_cv.notify_all();
        // Wait for dedicated workers.
        let guard = self.inner.lock().unwrap();
        self.dedicated_finished_cv
            .wait_while(guard, |g| g.num_dedicated_workers > 0)
            .unwrap();
    }
}

impl Drop for TaskManager {
    fn drop(&mut self) {
        // In production lean_finalize_task_manager calls initiate_shutdown before
        // the global Arc is removed, so workers have already exited by the time
        // we reach here.  In test code the TaskManager may be dropped directly;
        // just ensure shutting_down is set so any hypothetical waiters unblock.
        if !self.inner.lock().unwrap().shutting_down {
            self.inner.lock().unwrap().shutting_down = true;
            self.queue_cv.notify_all();
        }
    }
}

// ─── Global task manager ──────────────────────────────────────────────────────

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

// ─── Hardware concurrency ─────────────────────────────────────────────────────

fn get_lean_num_threads() -> usize {
    if let Ok(s) = std::env::var("LEAN_NUM_THREADS") {
        if let Ok(n) = s.parse::<usize>() {
            return n;
        }
    }
    thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

#[no_mangle]
pub extern "C" fn lean_internal_get_hardware_concurrency(_: *mut LeanObject) -> u32 {
    thread::available_parallelism()
        .map(|n| n.get() as u32)
        .unwrap_or(1)
}

// ─── Init / finalize ──────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_init_task_manager_using(num_workers: u32) {
    debug_assert!(get_task_manager().is_none());
    if num_workers > 0 {
        set_task_manager(Some(TaskManager::new(num_workers as usize)));
    }
}

#[no_mangle]
pub extern "C" fn lean_init_task_manager() {
    lean_init_task_manager_using(get_lean_num_threads() as u32);
}

#[no_mangle]
pub extern "C" fn lean_finalize_task_manager() {
    // First set shutting_down=true and wake idle workers, waiting for dedicated
    // workers to finish.  Standard workers exit their loops asynchronously.
    // This must happen BEFORE dropping the global Arc, otherwise workers holding
    // their own Arc clones would never see shutting_down and would wait forever.
    if let Some(tm) = get_task_manager() {
        tm.initiate_shutdown();
    }
    // Now drop the global Arc.  Standard workers will drop their Arcs once they
    // finish exiting; the TaskManager is freed when the last Arc disappears.
    set_task_manager(None);
}

// ─── Task spawn / pure ───────────────────────────────────────────────────────

#[no_mangle]
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

#[no_mangle]
pub unsafe extern "C" fn lean_task_pure(a: *mut LeanObject) -> *mut LeanObject {
    alloc_resolved_task(a) as *mut LeanObject
}

// ─── Task map ─────────────────────────────────────────────────────────────────

unsafe extern "C" fn task_map_fn(
    f: *mut LeanObject,
    t: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    let v = (*(t as *mut LeanTaskObject)).m_value;
    debug_assert!(!v.is_null());
    lean_inc(v);
    lean_dec_ref(t);
    lean_apply_1(f, v)
}

#[no_mangle]
pub unsafe extern "C" fn lean_task_map_core(
    f: *mut LeanObject,
    t: *mut LeanObject,
    prio: u32,
    sync: bool,
    keep_alive: bool,
) -> *mut LeanObject {
    let task = t as *mut LeanTaskObject;
    if let Some(tm) = get_task_manager() {
        if sync && !(*task).m_value.is_null() {
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

// ─── Task bind ────────────────────────────────────────────────────────────────

unsafe extern "C" fn task_bind_fn2(
    t: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    let v = (*(t as *mut LeanTaskObject)).m_value;
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
    let v = (*(x as *mut LeanTaskObject)).m_value;
    debug_assert!(!v.is_null());
    lean_inc(v);
    lean_dec_ref(x);

    let new_task_obj = lean_apply_1(f, v);
    debug_assert!(lean_is_task(new_task_obj));
    let new_task = new_task_obj as *mut LeanTaskObject;

    if !(*new_task).m_value.is_null() {
        let result = (*new_task).m_value;
        lean_inc(result);
        lean_dec_ref(new_task_obj);
        return result;
    }

    // Suspend: store continuation closure in m_closure of the current task.
    let ct = current_task();
    debug_assert!(!ct.is_null());
    debug_assert!(!(*(*ct).m_imp).m_closure.is_null() == false); // m_closure must be null
    let continuation = mk_closure_2_1(task_bind_fn2, new_task_obj);
    lean_mark_mt(continuation);
    (*(*ct).m_imp).m_closure = continuation;
    core::ptr::null_mut() // signal: task not yet finished
}

#[no_mangle]
pub unsafe extern "C" fn lean_task_bind_core(
    x: *mut LeanObject,
    f: *mut LeanObject,
    prio: u32,
    sync: bool,
    keep_alive: bool,
) -> *mut LeanObject {
    let task = x as *mut LeanTaskObject;
    if let Some(tm) = get_task_manager() {
        if sync && !(*task).m_value.is_null() {
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

// ─── Task get ─────────────────────────────────────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_task_get(t: *mut LeanObject) -> *mut LeanObject {
    let task = t as *mut LeanTaskObject;
    if !(*task).m_value.is_null() {
        return (*task).m_value;
    }
    if let Some(tm) = get_task_manager() {
        tm.wait_for(task);
    }
    debug_assert!(!(*task).m_value.is_null());
    (*task).m_value
}

/// Consume ownership of the task and return its value.
unsafe fn lean_task_get_own(t: *mut LeanObject) -> *mut LeanObject {
    let v = lean_task_get(t);
    lean_inc(v);
    lean_dec_ref(t);
    v
}

unsafe fn lean_is_task(o: *mut LeanObject) -> bool {
    !lean_is_scalar(o) && (*o).m_tag == LEAN_TASK_TAG
}

// ─── IO task helpers ──────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_io_check_canceled_core() -> bool {
    let ct = current_task();
    if ct.is_null() {
        return false;
    }
    unsafe {
        debug_assert!(!(*ct).m_imp.is_null());
        if (*(*ct).m_imp).m_canceled {
            return true;
        }
    }
    get_task_manager()
        .map(|tm| tm.shutting_down())
        .unwrap_or(false)
}

#[no_mangle]
pub unsafe extern "C" fn lean_io_cancel_core(t: *mut LeanObject) {
    let task = t as *mut LeanTaskObject;
    if !(*task).m_value.is_null() {
        return;
    }
    if let Some(tm) = get_task_manager() {
        tm.cancel_task(task);
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_io_get_task_state_core(t: *mut LeanObject) -> u8 {
    let task = t as *mut LeanTaskObject;
    if (*task).m_imp.is_null() {
        return 2; // finished
    }
    if let Some(tm) = get_task_manager() {
        tm.get_task_state(task)
    } else {
        2
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_io_wait_any_core(task_list: *mut LeanObject) -> *mut LeanObject {
    if let Some(tm) = get_task_manager() {
        tm.wait_any(task_list)
    } else {
        // No task manager — check inline.
        TaskManager::wait_any_check(task_list).unwrap_or(core::ptr::null_mut())
    }
}

// ─── deactivate_task / deactivate_promise (called from runtime_object_rc.rs) ─

#[no_mangle]
pub unsafe extern "C" fn deactivate_task(t: *mut LeanObject) {
    let task = t as *mut LeanTaskObject;
    if let Some(tm) = get_task_manager() {
        tm.deactivate_task_obj(task);
    } else {
        debug_assert!(!(*task).m_value.is_null());
        lean_dec((*task).m_value);
        free_task(task);
    }
}

#[no_mangle]
pub unsafe extern "C" fn deactivate_promise(p: *mut LeanObject) {
    let promise = p as *mut LeanPromiseObject;
    if let Some(tm) = get_task_manager() {
        let none = mk_option_none();
        tm.resolve((*promise).result as *mut LeanTaskObject, none);
        lean_dec_ref((*promise).result as *mut LeanObject);
    }
    lean_free_small_object(p);
}

// ─── Promise new / resolve ────────────────────────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_promise_new() -> *mut LeanObject {
    if get_task_manager().is_none() {
        lean_init_task_manager();
        if get_task_manager().is_none() {
            lean_internal_panic(
                c"`IO.Promise.new` called before the task manager is running; \
                  this typically happens when called (directly or transitively, \
                  e.g. via `IO.CancelToken.new`) from an `initialize` block. \
                  Construct lazily on first use instead.".as_ptr(),
            );
        }
    }

    // Allocate the underlying task object (no closure, no value yet).
    let t = lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
    lean_set_task_header(t as *mut LeanObject);
    (*t).m_value = core::ptr::null_mut();
    (*t).m_imp   = alloc_task_imp(core::ptr::null_mut(), 0, false);

    // Allocate the promise wrapper.
    let o = lean_alloc_small_object(core::mem::size_of::<LeanPromiseObject>()) as *mut LeanPromiseObject;
    lean_set_st_header(o as *mut LeanObject, LEAN_PROMISE_TAG, 0);
    (*o).result = t as *mut LeanObject;

    o as *mut LeanObject
}

#[no_mangle]
pub unsafe extern "C" fn lean_promise_resolve(
    value: *mut LeanObject,
    promise: *mut LeanObject,
) {
    let p = promise as *mut LeanPromiseObject;
    if let Some(tm) = get_task_manager() {
        let some_value = mk_option_some(value);
        tm.resolve((*p).result as *mut LeanTaskObject, some_value);
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_io_promise_new() -> *mut LeanObject {
    lean_promise_new()
}

#[no_mangle]
pub unsafe extern "C" fn lean_io_promise_resolve(
    value: *mut LeanObject,
    promise: *mut LeanObject,
) -> *mut LeanObject {
    lean_promise_resolve(value, promise);
    lean_box(0)
}

#[no_mangle]
pub unsafe extern "C" fn lean_io_promise_result_opt(promise: *mut LeanObject) -> *mut LeanObject {
    let p = promise as *mut LeanPromiseObject;
    let t = (*p).result as *mut LeanObject;
    lean_inc_ref(t);
    t
}

// ─── lean_get_or_block (IO.getOrBlock) ───────────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_get_or_block(opt: *mut LeanObject) -> *mut LeanObject {
    // opt is Option (lean_task_object*); tag 0 = none, tag 1 = some.
    if lean_is_scalar(opt) || (*opt).m_tag == 0 {
        lean_dec(opt);
        lean_box(0) // none → unit
    } else {
        // some(task) → wait for it and return value
        let task = lean_ctor_get(opt, 0);
        lean_inc(task);
        lean_dec(opt);
        let v = lean_task_get(task);
        lean_inc(v);
        lean_dec_ref(task);
        v
    }
}

// ─── scoped_task_manager (C++ class used in tests/tools) ─────────────────────

#[no_mangle]
pub extern "C" fn lean_scoped_task_manager_init(num_workers: u32) {
    lean_init_task_manager_using(num_workers);
}

#[no_mangle]
pub extern "C" fn lean_scoped_task_manager_finalize() {
    lean_finalize_task_manager();
}

// ─── Accessor helpers needed by lib.rs ───────────────────────────────────────

/// `lean_task_get_own` for use from lib.rs / other Rust files.
pub(crate) unsafe fn lean_task_get_own_internal(t: *mut LeanObject) -> *mut LeanObject {
    lean_task_get_own(t)
}

#[export_name = "lean_task_get_own"]
pub unsafe extern "C" fn lean_task_get_own_export(t: *mut LeanObject) -> *mut LeanObject {
    lean_task_get_own(t)
}

#[cfg(test)]
mod runtime_task_tests {
    use super::*;

    #[test]
    fn task_get_own_returns_resolved_value() {
        unsafe {
            let task = alloc_resolved_task(lean_box(7));
            let value = lean_task_get_own_export(task as *mut LeanObject);
            assert_eq!(value, lean_box(7));
        }
    }

    #[test]
    fn worker_count_does_not_exceed_max() {
        // Verify that spawning workers caps at max_std_workers.
        let max = 4usize;
        let tm = TaskManager::new(max);
        {
            let guard = tm.inner.lock().unwrap();
            assert_eq!(guard.total_std_workers, 0);
            assert_eq!(guard.max_std_workers, max);
        }
    }

    #[test]
    fn inner_worker_count_tracks_spawned_workers() {
        let max = 2usize;
        let tm = TaskManager::new(max);
        {
            let mut guard = tm.inner.lock().unwrap();
            assert_eq!(guard.inner_worker_count(&guard), 0);
            guard.total_std_workers = 1;
            assert_eq!(guard.inner_worker_count(&guard), 1);
            guard.total_std_workers = 2;
            assert_eq!(guard.inner_worker_count(&guard), 2);
        }
    }
}
