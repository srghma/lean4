use crate::{
    datatypes::LeanObject,
    emitted::{lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set},
};

// Mirrors origin-master-src/include/lean/lean.h:2952-2956 (`lean_io_result_mk_ok`).
#[inline]
pub unsafe fn lean_io_result_mk_ok(value: *mut LeanObject) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(obj, 0, value);
    obj
}
