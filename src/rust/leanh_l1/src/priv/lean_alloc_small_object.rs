use crate::{
    datatypes::LeanObject,
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic_out_of_memory,
};
use libmimalloc_sys as mi;

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`,
// `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn lean_alloc_small_object(sz: usize) -> *mut LeanObject {
    unsafe {
        let sz = sz.div_ceil(8) * 8;
        let mem = mi::mi_malloc_small(sz);
        if mem.is_null() {
            lean_internal_panic_out_of_memory();
        }
        let o = mem as *mut LeanObject;
        (*o).cs_size = sz as u16;
        o
    }
}
