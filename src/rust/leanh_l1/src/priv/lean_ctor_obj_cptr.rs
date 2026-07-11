use crate::{
    datatypes::{LeanCtorObject, LeanObject},
    r#priv::lean_to_ctor::lean_to_ctor,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`,
// `lean_box_float`, `lean_box_float32`, and 32 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_obj_cptr(obj: *const LeanObject) -> *mut *mut LeanObject {
    unsafe {
        (*(lean_to_ctor(obj) as *mut LeanCtorObject<0>))
            .m_objs
            .as_mut_ptr()
    }
}
