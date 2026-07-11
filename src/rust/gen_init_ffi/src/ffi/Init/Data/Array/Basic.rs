use leanh::LeanObject;
use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/Array/Basic.lean

pub use leanh_l1::r#priv::lean_array_size::lean_array_size;

pub use cargo::lean_array_uget;

pub unsafe fn lean_array_uget_borrowed(array: *mut LeanObject, idx: usize) -> *mut LeanObject {
    unsafe { leanh::lean_array_uget_borrowed(array, idx) }
}

pub unsafe fn lean_array_uset(
    array: *mut LeanObject,
    idx: usize,
    value: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_uset(array, idx, value) }
}

pub unsafe fn lean_array_pop(array: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_array_pop(array) }
}

pub unsafe fn lean_mk_array(n: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_mk_array(n, value) }
}

pub unsafe fn lean_array_fswap(
    array: *mut LeanObject,
    i: *mut LeanObject,
    j: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_fswap(array, i, j) }
}

pub unsafe fn lean_array_swap(
    array: *mut LeanObject,
    i: *mut LeanObject,
    j: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_swap(array, i, j) }
}
