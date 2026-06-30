// Generated stub file for Lean FFI imports
// Source: src/Init/Data/Int/Basic.lean

use leanh::LeanObject;
use runtime::leanh_extra as leanh;

pub unsafe fn lean_nat_to_int(value: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_to_int(value) }
}

pub fn lean_int_neg_succ_of_nat(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_int_neg_succ_of_nat");
}

pub unsafe fn lean_int_neg(value: *mut LeanObject) -> *mut LeanObject {
    if unsafe { leanh::lean_unbox(value) } == 0 {
        value
    } else {
        todo!("Stub for lean_int_neg");
    }
}

pub unsafe fn lean_int_add(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_add(a, b) }
}

pub unsafe fn lean_int_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_mul(a, b) }
}

pub unsafe fn lean_int_sub(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    let av = unsafe { leanh::lean_unbox(a) };
    let bv = unsafe { leanh::lean_unbox(b) };
    if av >= bv {
        unsafe { leanh::lean_box(av - bv) }
    } else {
        todo!("Stub for negative lean_int_sub");
    }
}

pub unsafe fn lean_int_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_nat_dec_eq(a, b) }
}

pub unsafe fn lean_int_dec_nonneg(_: *mut LeanObject) -> u8 {
    1
}

pub unsafe fn lean_int_dec_le(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_nat_dec_le(a, b) }
}

pub unsafe fn lean_int_dec_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_nat_dec_lt(a, b) }
}

pub unsafe fn lean_nat_abs(value: *mut LeanObject) -> *mut LeanObject {
    value
}