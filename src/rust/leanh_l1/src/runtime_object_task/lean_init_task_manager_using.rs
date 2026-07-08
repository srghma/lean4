use crate::runtime_object_task::p1_get_task_manager::get_task_manager;
pub fn lean_init_task_manager_using(num_workers: usize) {
    debug_assert!(get_task_manager().is_none());
    #[cfg(lean_multi_thread)]
    if num_workers > 0 {
        use crate::runtime_object_task::{
            new_task_manager::new_task_manager, p1_get_task_manager::set_task_manager,
        };

        set_task_manager(Some(new_task_manager(num_workers)));
    }
    #[cfg(not(lean_multi_thread))]
    let _ = num_workers;
}
