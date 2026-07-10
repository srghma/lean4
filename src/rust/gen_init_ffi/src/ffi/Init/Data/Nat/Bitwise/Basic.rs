use leanh::LeanObject;
use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/Nat/Bitwise/Basic.lean

pub unsafe fn lean_nat_land(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_box(leanh::lean_unbox(a) & leanh::lean_unbox(b)) }
}

pub unsafe fn lean_nat_lor(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_box(leanh::lean_unbox(a) | leanh::lean_unbox(b)) }
}

pub unsafe fn lean_nat_lxor(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_box(leanh::lean_unbox(a) ^ leanh::lean_unbox(b)) }
}

pub unsafe fn lean_nat_shiftl(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_box(leanh::lean_unbox(a) << leanh::lean_unbox(b)) }
}

pub unsafe fn lean_nat_shiftr(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_shiftr(a, b) }
}
