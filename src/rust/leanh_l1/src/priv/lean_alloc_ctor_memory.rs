use crate::{datatypes::LeanObject, r#priv::lean_alloc_small_object::lean_alloc_small_object};

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`,
// `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn lean_alloc_ctor_memory(sz: usize) -> *mut LeanObject {
    let sz1 = sz.div_ceil(8) * 8;
    let r = unsafe { lean_alloc_small_object(sz1) };
    if sz1 > sz {
        let end = unsafe { (r as *mut u8).add(sz1) as *mut usize };
        unsafe { end.sub(1).write(0) };
    }
    r
}
