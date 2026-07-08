use std::ffi::c_void;

use crate::{
    datatypes::LeanObject,
    r#priv::quar::{UAF_DETECT, quar_free},
};

use libmimalloc_sys as mi;

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_free_small_object(o: *mut LeanObject) {
    if UAF_DETECT {
        unsafe { quar_free(o) };
        return;
    }
    unsafe { mi::mi_free_small(o as *mut c_void) };
}
