use std::ptr;

use crate::{datatypes::LeanObject, lean_alloc_ctor::lean_alloc_ctor};

#[inline]
pub unsafe fn lean_box_float(value: f64) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f64>() as u32);
        ptr::write_unaligned(
            (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f64,
            value,
        );

        // lean_ctor_set_float(obj, 0, value);
        obj
    }
}
