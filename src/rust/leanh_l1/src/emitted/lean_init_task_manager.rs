use crate::{
    r#priv::get_lean_num_threads::get_lean_num_threads,
    runtime_object_task::lean_init_task_manager_using::lean_init_task_manager_using,
};

pub fn lean_init_task_manager() {
    lean_init_task_manager_using(get_lean_num_threads());
}
