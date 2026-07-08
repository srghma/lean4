use crate::datatypes::{LeanObject, LeanTaskImp, LeanTaskObject};
use crate::emitted::lean_box::lean_box;
use crate::emitted::lean_dec::lean_dec;
use crate::emitted::lean_dec_ref::lean_dec_ref;
use crate::r#priv::free_task::free_task;
use crate::r#priv::free_task_imp::free_task_imp;
use crate::r#priv::lean_closure_arg_cptr::lean_closure_arg_cptr;
use crate::runtime_apply::lean_apply_1;
use crate::runtime_interrupt::reset_heartbeat;
use crate::runtime_object_rc::lean_mark_mt::lean_mark_mt;
use crate::runtime_object_task::p2_deactivate_task_obj::with_mutex_unlocked;
use crate::runtime_object_task::scoped_current_task::ScopedCurrentTask;
use crate::runtime_object_task::task_manager::{LEAN_MAX_PRIO, TaskManager, TaskManagerInner};
use crate::runtime_stack_info::save_stack_info;
use crate::runtime_stack_overflow::p1::{
    StackGuard, stack_guard_ctor_complete, stack_guard_dtor_complete,
};
use crate::runtime_thread::p1::{lean_finalize_thread, lean_initialize_thread};
use std::mem::MaybeUninit;
use std::sync::atomic::Ordering;
use std::sync::{Arc, MutexGuard};
use std::thread::JoinHandle;

pub const LEAN_SYNC_PRIO: u32 = u32::MAX;

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

unsafe fn add_dep_raw(slf: &Arc<TaskManager>, t1: *mut LeanTaskObject, t2: *mut LeanTaskObject) {
    let mut guard = slf.inner.lock().unwrap();
    if !(*t1).m_value.load(Ordering::Acquire).is_null() {
        enqueue_core(slf, &mut guard, t2);
        return;
    }
    let t2_imp = (*t2).m_imp as *mut LeanTaskImp;
    let t1_imp = (*t1).m_imp as *mut LeanTaskImp;
    (*t2_imp).m_next_dep = (*t1_imp).m_head_dep;
    (*t1_imp).m_head_dep = t2;
}

fn run_task_locked<'a>(
    slf: &'a Arc<TaskManager>,
    guard: &mut MutexGuard<'a, TaskManagerInner>,
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

    let result = with_mutex_unlocked!(guard, slf.inner, {
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
        with_mutex_unlocked!(guard, slf.inner, {
            if !result.is_null() {
                lean_dec(result);
            }
            free_task(t);
        });
    } else if !result.is_null() {
        resolve_core(slf, guard, t, result);
    } else {
        // Bind task suspended — re-registered as dep of a nested task.
        // The closure pointer was updated by task_bind_fn1.
        let new_closure = unsafe { (*imp3).m_closure };
        with_mutex_unlocked!(guard, slf.inner, {
            let nested_ptr = lean_closure_arg_cptr(new_closure) as *mut *mut LeanTaskObject;
            let nested = *nested_ptr;
            add_dep_raw(slf, nested, t);
        });
    }
}

fn spawn_dedicated_worker(
    slf: &Arc<TaskManager>,
    guard: &mut MutexGuard<'_, TaskManagerInner>,
    t: *mut LeanTaskObject,
) {
    guard.num_dedicated_workers += 1;
    let tm = Arc::clone(slf);
    let t_send = SendPtr(t);
    spawn_lean_worker(move || {
        unsafe {
            save_stack_info(false);
        }
        let mut guard = tm.inner.lock().unwrap();
        run_task_locked(&tm, &mut guard, t_send.get());
        guard.num_dedicated_workers -= 1;
        tm.dedicated_finished_cv.notify_all();
    });
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

pub fn spawn_worker(slf: &Arc<TaskManager>, guard: &mut MutexGuard<'_, TaskManagerInner>) {
    if guard.shutting_down {
        return;
    }
    guard.total_std_workers += 1;
    let tm = Arc::clone(slf);
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
            let t = dequeue(&mut guard);
            guard.idle_std_workers -= 1;
            run_task_locked(&tm, &mut guard, t);
            guard.idle_std_workers += 1;
            reset_heartbeat();
        }
        guard.idle_std_workers -= 1;
        guard.total_std_workers -= 1;
    });
    guard.std_workers.push(handle);
}

fn enqueue_core<'a>(
    slf: &'a Arc<TaskManager>,
    guard: &mut MutexGuard<'a, TaskManagerInner>,
    t: *mut LeanTaskObject,
) {
    let prio = unsafe { (*((*t).m_imp as *mut LeanTaskImp)).m_prio };

    if prio == LEAN_SYNC_PRIO {
        run_task_locked(slf, guard, t);
        return;
    }
    if prio > LEAN_MAX_PRIO {
        spawn_dedicated_worker(slf, guard, t);
        return;
    }
    let prio_idx = prio as usize;
    if prio_idx > guard.max_prio {
        guard.max_prio = prio_idx;
    }
    guard.queues[prio_idx].push_back(t);
    guard.queues_size += 1;

    if guard.idle_std_workers == 0 && guard.total_std_workers < guard.max_std_workers {
        spawn_worker(slf, guard);
    } else {
        slf.queue_cv.notify_one();
    }
}

fn handle_finished<'a>(
    slf: &'a Arc<TaskManager>,
    guard: &mut MutexGuard<'a, TaskManagerInner>,
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
            enqueue_core(slf, guard, it);
        }
        it = next;
    }
}

fn resolve_core<'a>(
    slf: &'a Arc<TaskManager>,
    guard: &mut MutexGuard<'a, TaskManagerInner>,
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
    handle_finished(slf, guard, t, imp);
    unsafe {
        free_task_imp(imp);
    }
    slf.task_finished_cv.notify_all();
}

pub unsafe fn resolve(slf: &Arc<TaskManager>, t: *mut LeanTaskObject, v: *mut LeanObject) {
    if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
        unsafe {
            lean_dec(v);
        }
        return;
    }
    let mut guard = slf.inner.lock().unwrap();
    if !unsafe { (*t).m_value.load(Ordering::Acquire).is_null() } {
        drop(guard);
        unsafe {
            lean_dec(v);
        }
        return;
    }
    resolve_core(slf, &mut guard, t, v);
}
