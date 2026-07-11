use leanh_l1::{
    datatypes::{LeanObject, LeanTaskObject},
    emitted::{lean_dec_ref::lean_dec_ref, lean_inc::lean_inc},
    runtime_apply::lean_apply_1,
};
use std::sync::atomic::Ordering;

// ─── Task map ─────────────────────────────────────────────────────────────

pub unsafe fn task_map_fn(
    f: *mut LeanObject,
    t: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    // Actually we need the value, not imp:
    let v = (*(t as *mut LeanTaskObject))
        .m_value
        .load(Ordering::Relaxed);
    debug_assert!(!v.is_null());
    lean_inc(v);
    lean_dec_ref(t);
    lean_apply_1(f, v)
}
