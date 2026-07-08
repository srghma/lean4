use crate::{
    datatypes::{LEAN_MAX_CTOR_TAG, LeanObject},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

// Mirrors origin-master-src/include/lean/lean.h:708-711 (`lean_ctor_set_tag`).
#[inline]
pub unsafe fn lean_ctor_set_tag(obj: *mut LeanObject, new_tag: u8) {
    debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
    debug_assert!(new_tag <= LEAN_MAX_CTOR_TAG);
    (*obj).tag = new_tag;
}
