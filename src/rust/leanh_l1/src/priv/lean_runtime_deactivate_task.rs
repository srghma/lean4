// ─── Deactivate task / promise (called from runtime_object_rc.rs) ─────────

use std::sync::atomic::Ordering;

use crate::{
    datatypes::LeanTaskObject,
    lean_dec::lean_dec,
    r#priv::free_task::free_task,
    runtime_object_task::{
        p1_get_task_manager::get_task_manager, p2_deactivate_task_obj::deactivate_task_obj,
    },
};
pub unsafe fn lean_runtime_deactivate_task(t: *mut LeanTaskObject) {
    if let Some(tm) = get_task_manager() {
        unsafe { deactivate_task_obj(&tm, t) };
    } else {
        let v = unsafe { (*t).m_value.load(Ordering::Acquire) };
        debug_assert!(!v.is_null());
        unsafe { lean_dec(v) };
        unsafe { free_task(t) };
    }
}
