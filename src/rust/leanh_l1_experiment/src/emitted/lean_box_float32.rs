use std::ptr;

use crate::{datatypes::LeanObject, emitted::lean_alloc_ctor::lean_alloc_ctor};

#[inline(always)]
pub unsafe fn lean_box_float32(v: f32) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f32>() as u32);
        // lean_ctor_set_float32(obj, 0, value);
        ptr::write_unaligned(
            (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f32,
            v,
        );
        obj
    }
}
