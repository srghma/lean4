use leanh_l1::{
    datatypes::{LeanObject, LeanTaskObject},
    emitted::lean_inc_ref::lean_inc_ref,
    r#priv::lean_alloc_small_object::lean_alloc_small_object,
    runtime_object_rc::lean_mark_mt::lean_mark_mt,
};
use std::{ffi::c_void, sync::atomic::AtomicPtr};

use crate::r#priv::{alloc_task_imp::alloc_task_imp, set_task_header_mt::set_task_header_mt};

// Allocate a running task (has closure, no value yet, MT header).
pub unsafe fn alloc_running_task(
    closure: *mut LeanObject,
    prio: u32,
    keep_alive: bool,
) -> *mut LeanTaskObject {
    lean_mark_mt(closure);
    let o = lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
    set_task_header_mt(o as *mut LeanObject);
    (*o).m_value = AtomicPtr::new(core::ptr::null_mut());
    (*o).m_imp = alloc_task_imp(closure, prio, keep_alive) as *mut c_void;
    if keep_alive {
        lean_inc_ref(o as *const LeanObject);
    }
    o
}
