use crate::datatypes::{LeanObject, LeanPromiseObject, LeanTaskImp, LeanTaskObject};
use crate::in_emit_rust::{lean_dec, lean_dec_ref};
use crate::not_in_emit_rust::{lean_box, lean_free_small_object};
use crate::runtime_apply::lean_apply_1;
use crate::runtime_interrupt::reset_heartbeat;
use crate::runtime_object_panic::lean_panic;
use crate::runtime_object_rc::lean_mark_mt;
use crate::runtime_stack_info::save_stack_info;
use crate::runtime_stack_overflow::{
    StackGuard, stack_guard_ctor_complete, stack_guard_dtor_complete,
};
use crate::runtime_thread::{lean_finalize_thread, lean_initialize_thread};
use core::ffi::c_void;
use std::collections::VecDeque;
use std::mem::MaybeUninit;
use std::sync::atomic::Ordering;
use std::sync::{Arc, Condvar, Mutex, MutexGuard};
use std::thread::JoinHandle;
const LEAN_MAX_PRIO: u32 = 8;
const LEAN_SYNC_PRIO: u32 = u32::MAX;

#[inline(always)]
unsafe fn mk_option_none() -> *mut LeanObject {
    unsafe { lean_box(0) }
}

// ─── Helper: send raw pointer across threads ──────────────────────────────

struct SendPtr<T>(*mut T);
unsafe impl<T> Send for SendPtr<T> {}
impl<T> SendPtr<T> {
    #[inline]
    fn get(&self) -> *mut T {
        self.0
    }
}

// ─── Worker thread spawning ───────────────────────────────────────────────

fn spawn_lean_worker<F: FnOnce() + Send + 'static>(f: F) -> JoinHandle<()> {
    const STACK_SIZE: usize = 1024 * 1024 * 1024; // 1 GB

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

unsafe fn free_task_imp(imp: *mut LeanTaskImp) {
    unsafe { lean_free_small_object(imp as *mut LeanObject) };
}

unsafe fn free_task(t: *mut LeanTaskObject) {
    let imp = unsafe { (*t).m_imp as *mut LeanTaskImp };
    if !imp.is_null() {
        unsafe { free_task_imp(imp) };
    }
    unsafe { lean_free_small_object(t as *mut LeanObject) };
}

#[inline(always)]
unsafe fn local_closure_arg_cptr(o: *mut LeanObject) -> *mut *mut LeanObject {
    (*(o as *mut LeanClosureLocal)).data.as_mut_ptr()
}

impl TaskManager {
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

    fn deactivate_task_core(
        self: &Arc<Self>,
        guard: &mut MutexGuard<'_, TaskManagerInner>,
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
        with_mutex_unlocked!(guard, self.inner, {
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

    fn deactivate_task_obj(self: &Arc<Self>, t: *mut LeanTaskObject) {
        let mut guard = self.inner.lock().unwrap();
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
        self.deactivate_task_core(&mut guard, t);
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

    fn enqueue_core(
        self: &Arc<Self>,
        guard: &mut MutexGuard<'_, TaskManagerInner>,
        t: *mut LeanTaskObject,
    ) {
        let prio = unsafe { (*((*t).m_imp as *mut LeanTaskImp)).m_prio };

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
            let it_imp = unsafe { (*it).m_imp as *mut LeanTaskImp };
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
            (*t).m_value.store(v, Ordering::Release);
        }
        let imp = unsafe {
            let imp = (*t).m_imp as *mut LeanTaskImp;
            (*t).m_imp = core::ptr::null_mut();
            imp
        };
        self.handle_finished(guard, t, imp);
        unsafe {
            free_task_imp(imp);
        }
        self.task_finished_cv.notify_all();
    }

    fn resolve(self: &Arc<Self>, t: *mut LeanTaskObject, v: *mut LeanObject) {
        if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
            unsafe {
                lean_dec(v);
            }
            return;
        }
        let mut guard = self.inner.lock().unwrap();
        if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
            drop(guard);
            unsafe {
                lean_dec(v);
            }
            return;
        }
        self.resolve_core(&mut guard, t, v);
    }

    fn run_task_locked(
        self: &Arc<Self>,
        guard: &mut MutexGuard<'_, TaskManagerInner>,
        t: *mut LeanTaskObject,
    ) {
        let imp = unsafe { (*t).m_imp as *mut LeanTaskImp };
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
                let imp2 = (*t).m_imp as *mut LeanTaskImp;
                if (*imp2).m_keep_alive {
                    lean_dec_ref(t as *mut LeanObject);
                }
            }
            result
        });

        let imp3 = unsafe { (*t).m_imp as *mut LeanTaskImp };
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
                let nested_ptr = local_closure_arg_cptr(new_closure) as *mut *mut LeanTaskObject;
                let nested = *nested_ptr;
                self.add_dep_raw(nested, t);
            });
        }
    }

    unsafe fn add_dep_raw(self: &Arc<Self>, t1: *mut LeanTaskObject, t2: *mut LeanTaskObject) {
        let mut guard = self.inner.lock().unwrap();
        if !(*t1).m_value.load(Ordering::Acquire).is_null() {
            self.enqueue_core(&mut guard, t2);
            return;
        }
        let t2_imp = (*t2).m_imp as *mut LeanTaskImp;
        let t1_imp = (*t1).m_imp as *mut LeanTaskImp;
        (*t2_imp).m_next_dep = (*t1_imp).m_head_dep;
        (*t1_imp).m_head_dep = t2;
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

    fn wait_for(self: &Arc<Self>, t: *mut LeanTaskObject) {
        if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
            return;
        }
        let mut guard = self.inner.lock().unwrap();
        if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
            return;
        }

        let ct = current_task();
        let in_pool = !ct.is_null()
            && unsafe { (*((*ct).m_imp as *mut LeanTaskImp)).m_prio <= LEAN_MAX_PRIO };

        if !ct.is_null() {
            let ct_imp = unsafe { (*ct).m_imp as *mut LeanTaskImp };
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
                (*t).m_value.load(Ordering::Acquire).is_null()
            })
            .unwrap();

        if in_pool {
            guard.max_std_workers -= 1;
        }
    }
}

pub unsafe fn lean_task_get(t: *mut LeanObject) -> *mut LeanObject {
    let task = t as *mut LeanTaskObject;
    let v = (*task).m_value.load(Ordering::Acquire);
    if !v.is_null() {
        return v;
    }
    if let Some(tm) = get_task_manager() {
        tm.wait_for(task);
    }
    let v2 = (*task).m_value.load(Ordering::Acquire);
    debug_assert!(!v2.is_null());
    v2
}

static G_TASK_MANAGER: std::sync::OnceLock<std::sync::Mutex<Option<Arc<TaskManager>>>> =
    std::sync::OnceLock::new();

fn task_manager_cell() -> &'static std::sync::Mutex<Option<Arc<TaskManager>>> {
    G_TASK_MANAGER.get_or_init(|| std::sync::Mutex::new(None))
}

fn get_task_manager() -> Option<Arc<TaskManager>> {
    task_manager_cell().lock().unwrap().clone()
}
pub unsafe fn lean_runtime_deactivate_task(t: *mut LeanTaskObject) {
    if let Some(tm) = get_task_manager() {
        tm.deactivate_task_obj(t);
    } else {
        let v = unsafe { (*t).m_value.load(Ordering::Acquire) };
        debug_assert!(!v.is_null());
        unsafe { lean_dec(v) };
        unsafe { free_task(t) };
    }
}

pub unsafe fn lean_runtime_deactivate_promise(promise: *mut LeanPromiseObject) {
    if let Some(tm) = get_task_manager() {
        let none = unsafe { mk_option_none() };
        tm.resolve((*promise).m_result as *mut LeanTaskObject, none);
        unsafe {
            let task = (*promise).m_result;
            lean_dec_ref(core::ptr::addr_of_mut!((*task).m_header));
        }
    }
    unsafe { lean_free_small_object(promise as *mut LeanObject) };
}
