use crate::datatypes::LeanTaskObject;
use std::collections::VecDeque;
use std::sync::{Condvar, Mutex};
use std::thread::JoinHandle;

pub const LEAN_MAX_PRIO: u32 = 8;

// ─── Task manager internals ───────────────────────────────────────────────

pub struct TaskManagerInner {
    pub queues: [VecDeque<*mut LeanTaskObject>; (LEAN_MAX_PRIO + 1) as usize],
    pub queues_size: usize,
    pub max_prio: usize,
    pub max_std_workers: usize,
    pub std_workers: Vec<JoinHandle<()>>,
    pub total_std_workers: usize,
    pub idle_std_workers: usize,
    pub num_dedicated_workers: usize,
    pub shutting_down: bool,
}

// SAFETY: task object pointers are shared under the mutex.
unsafe impl Send for TaskManagerInner {}

pub struct TaskManager {
    pub inner: Mutex<TaskManagerInner>,
    pub queue_cv: Condvar,
    pub task_finished_cv: Condvar,
    pub dedicated_finished_cv: Condvar,
}

unsafe impl Send for TaskManager {}
unsafe impl Sync for TaskManager {}

impl Drop for TaskManager {
    fn drop(&mut self) {
        if !self.inner.lock().unwrap().shutting_down {
            self.inner.lock().unwrap().shutting_down = true;
            self.queue_cv.notify_all();
        }
    }
}
