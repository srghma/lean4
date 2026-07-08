use crate::runtime_object_task::task_manager::TaskManager;
use std::sync::Arc;

static G_TASK_MANAGER: std::sync::OnceLock<std::sync::Mutex<Option<Arc<TaskManager>>>> =
    std::sync::OnceLock::new();

fn task_manager_cell() -> &'static std::sync::Mutex<Option<Arc<TaskManager>>> {
    G_TASK_MANAGER.get_or_init(|| std::sync::Mutex::new(None))
}

pub fn get_task_manager() -> Option<Arc<TaskManager>> {
    task_manager_cell().lock().unwrap().clone()
}

pub fn set_task_manager(tm: Option<Arc<TaskManager>>) {
    *task_manager_cell().lock().unwrap() = tm;
}
