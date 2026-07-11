use crate::{
    datatypes::{LeanArrayObject, LeanObject},
    r#priv::lean_to_array::lean_to_array,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe {
        (*(lean_to_array(obj) as *mut LeanArrayObject<0>))
            .m_data
            .as_mut_ptr()
    }
}
