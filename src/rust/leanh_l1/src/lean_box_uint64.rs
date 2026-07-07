use std::ffi::c_uint;

use crate::{
    datatypes::LeanObject, lean_alloc_ctor::lean_alloc_ctor,
    lean_ctor_set_uint64::lean_ctor_set_uint64,
};

#[inline]
pub unsafe fn lean_box_uint64(v: u64) -> *mut LeanObject {
    unsafe {
        let r = lean_alloc_ctor(0, 0, core::mem::size_of::<u64>() as c_uint);
        lean_ctor_set_uint64(r, 0, v);
        r
    }
}
