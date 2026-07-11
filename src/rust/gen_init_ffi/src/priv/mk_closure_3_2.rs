use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_alloc_closure::lean_alloc_closure, lean_closure_set::lean_closure_set},
};
use std::ffi::c_void;

#[inline(always)]
pub unsafe fn mk_closure_3_2(
    fun: unsafe fn(*mut LeanObject, *mut LeanObject, *mut LeanObject) -> *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    let c = lean_alloc_closure(fun as *mut c_void, 3, 2);
    lean_closure_set(c, 0, a1);
    lean_closure_set(c, 1, a2);
    c
}
