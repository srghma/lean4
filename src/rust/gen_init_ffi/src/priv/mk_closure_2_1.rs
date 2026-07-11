use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_alloc_closure::lean_alloc_closure, lean_closure_set::lean_closure_set},
};
use std::ffi::c_void;

#[inline(always)]
pub unsafe fn mk_closure_2_1(
    fun: unsafe fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let c = lean_alloc_closure(fun as *mut c_void, 2, 1);
    lean_closure_set(c, 0, a);
    c
}
