use crate::{datatypes::LeanObject, r#priv::lean_is_ctor::lean_is_ctor};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`,
// `lean_box_float`, `lean_box_float32`, and 32 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_obj_cptr(obj: *const LeanObject) -> *mut *mut LeanObject {
    unsafe {
        debug_assert!(lean_is_ctor(obj));
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut *mut LeanObject
    }
}
