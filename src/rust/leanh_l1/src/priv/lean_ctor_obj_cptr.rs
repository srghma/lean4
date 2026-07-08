use crate::{
    datatypes::{LEAN_MAX_CTOR_TAG, LeanObject},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`,
// `lean_box_float`, `lean_box_float32`, and 32 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_obj_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe {
        debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut *mut LeanObject
    }
}
