use crate::{
    r#priv::lean_runtime_get_lean_num_threads::lean_runtime_get_lean_num_threads,
    runtime_object_task::lean_init_task_manager_using::lean_init_task_manager_using,
};

pub fn lean_init_task_manager() {
    lean_init_task_manager_using(lean_runtime_get_lean_num_threads());
}
