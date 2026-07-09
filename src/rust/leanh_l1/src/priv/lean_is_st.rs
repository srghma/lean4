use crate::datatypes::LeanObject;

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`, `lean_inc`, `lean_inc_n`, `lean_inc_ref`, and 2 more EmitRust functions.
#[inline]
pub unsafe fn lean_is_st(obj: *const LeanObject) -> bool {
    unsafe { (*obj).rc > 0 }
}
