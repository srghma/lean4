use crate::{
    datatypes::LeanObject,
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic_out_of_memory,
};
use libmimalloc_sys as mi;
pub unsafe fn lean_alloc_object(sz: usize) -> *mut LeanObject {
    let r = mi::mi_malloc(sz);
    if r.is_null() {
        lean_internal_panic_out_of_memory();
    }
    let o = r as *mut LeanObject;
    (*o).cs_size = 0;
    o
}
