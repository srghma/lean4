use crate::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::lean_is_scalar::lean_is_scalar,
    emitted::lean_unbox::lean_unbox,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`,
// `lean_box_float`, `lean_box_float32`, and 37 more EmitRust functions.
#[inline]
pub unsafe fn lean_ptr_tag(obj: *const LeanObject) -> LeanObjectTag {
    if lean_is_scalar(obj) {
        LeanObjectTag::Ctor(lean_unbox(obj) as u8)
    } else {
        (*obj).tag()
    }
}
