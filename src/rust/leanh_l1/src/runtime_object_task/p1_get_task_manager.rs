use crate::datatypes::LeanTaskObject;
use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
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

static G_TASK_MANAGER: std::sync::OnceLock<std::sync::Mutex<Option<Arc<TaskManager>>>> =
    std::sync::OnceLock::new();

fn task_manager_cell() -> &'static std::sync::Mutex<Option<Arc<TaskManager>>> {
    G_TASK_MANAGER.get_or_init(|| std::sync::Mutex::new(None))
}

pub fn get_task_manager() -> Option<Arc<TaskManager>> {
    task_manager_cell().lock().unwrap().clone()
}
