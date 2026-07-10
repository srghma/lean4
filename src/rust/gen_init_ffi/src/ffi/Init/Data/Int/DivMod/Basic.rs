use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/Int/DivMod/Basic.lean

pub unsafe fn lean_int_ediv(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_nat_div(a, b) }
}

pub unsafe fn lean_int_emod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_nat_mod(a, b) }
}

pub fn lean_int_div_exact(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_int_div_exact");
}

pub fn lean_int_div(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_int_div");
}

pub fn lean_int_mod(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_int_mod");
}
