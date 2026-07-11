use leanh_l1::{
    datatypes::{LeanObject, LeanTaskObject},
    emitted::{lean_dec_ref::lean_dec_ref, lean_inc::lean_inc},
};
use std::sync::atomic::Ordering;

// ─── Task bind ────────────────────────────────────────────────────────────

pub unsafe fn task_bind_fn2(t: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
    let v = (*(t as *mut LeanTaskObject))
        .m_value
        .load(Ordering::Relaxed);
    debug_assert!(!v.is_null());
    lean_inc(v);
    lean_dec_ref(t);
    v
}
