use crate::runtime_object_task::{
    initiate_shutdown::initiate_shutdown,
    p1_get_task_manager::{get_task_manager, set_task_manager},
};

pub fn lean_finalize_task_manager() {
    if let Some(tm) = get_task_manager() {
        initiate_shutdown(&tm);
    }
    set_task_manager(None);
}
