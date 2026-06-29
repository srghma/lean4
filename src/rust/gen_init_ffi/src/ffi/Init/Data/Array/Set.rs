use crate::leanh::LeanObject;
use runtime::leanh_extra as leanh;
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/Array/Set.lean

pub unsafe fn lean_array_fset(
    array: *mut LeanObject,
    idx: *mut LeanObject,
    value: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_fset(array, idx, value) }
}

pub unsafe fn lean_array_set(
    array: *mut LeanObject,
    idx: *mut LeanObject,
    value: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_set(array, idx, value) }
}
