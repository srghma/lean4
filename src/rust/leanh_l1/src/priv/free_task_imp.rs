// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_task.rs:195-198

use crate::{
    datatypes::{LeanObject, LeanTaskImp},
    r#priv::lean_free_small_object::lean_free_small_object,
};

pub unsafe fn free_task_imp(imp: *mut LeanTaskImp) {
    unsafe { lean_free_small_object(imp as *mut LeanObject) };
}
