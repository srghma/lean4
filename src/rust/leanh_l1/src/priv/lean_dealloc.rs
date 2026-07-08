use libmimalloc_sys as mi;
use std::ffi::c_void;

use crate::{
    datatypes::LeanObject,
    r#priv::quar::{UAF_DETECT, quar_free},
};

#[inline(always)]
pub unsafe fn lean_dealloc(o: *mut LeanObject, sz: usize) {
    unsafe {
        if UAF_DETECT {
            quar_free(o);
            return;
        }
        mi::mi_free_size(o as *mut c_void, sz);
    }
}
