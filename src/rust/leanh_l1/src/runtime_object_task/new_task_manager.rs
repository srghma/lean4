use crate::runtime_object_task::task_manager::{TaskManager, TaskManagerInner};
use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
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
