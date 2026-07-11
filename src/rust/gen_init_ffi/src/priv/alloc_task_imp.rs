use leanh_l1::{
    datatypes::{LeanObject, LeanTaskImp},
    r#priv::lean_alloc_small_object::lean_alloc_small_object,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_task.rs:177-194 and from src/rust/runtime/src/runtime_object_task.rs:66-83

// ─── Task allocation helpers ──────────────────────────────────────────────

pub(crate) unsafe fn alloc_task_imp(
    closure: *mut LeanObject,
    prio: u32,
    keep_alive: bool,
) -> *mut LeanTaskImp {
    let imp = lean_alloc_small_object(core::mem::size_of::<LeanTaskImp>()) as *mut LeanTaskImp;
    (*imp).m_closure = closure;
    (*imp).m_head_dep = core::ptr::null_mut();
    (*imp).m_next_dep = core::ptr::null_mut();
    (*imp).m_prio = prio;
    (*imp).m_canceled = false;
    (*imp).m_keep_alive = keep_alive;
    (*imp).m_deleted = false;
    imp
}
