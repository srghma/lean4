use leanh_l1::datatypes::{LeanObject, LeanStringObject};

// ── local inline helpers ─────────────────────────────────────────────────────

#[inline]
pub unsafe fn lean_string_capacity(o: *const LeanObject) -> usize {
    (*(o as *const LeanStringObject<0>)).m_capacity
}
