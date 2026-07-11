// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:80-82
// exact-text variant: no

use crate::ffi::Init::Prelude::lean_nat_add;
use leanh_l1::datatypes::LeanObject;

use leanh_l1::emitted::lean_box::lean_box;
use leanh_l1::emitted::lean_is_scalar::lean_is_scalar;
use leanh_l1::emitted::lean_unbox::lean_unbox;
use leanh_l1::r#priv::lean_string_cstr::lean_string_cstr;
use leanh_l1::r#priv::lean_string_size::lean_string_size;
use leanh_l1::r#priv::lean_usize_to_nat::lean_usize_to_nat;
pub unsafe fn lean_string_utf8_next(s: *mut LeanObject, i0: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(i0) {
        return lean_nat_add(i0, lean_box(1));
    }
    let i = lean_unbox(i0);
    let str = lean_string_cstr(s) as *const u8;
    let size = lean_string_size(s) - 1;
    if i >= size {
        return lean_usize_to_nat(i + 1);
    }
    let c = *str.add(i);
    if (c & 0x80) == 0 {
        return lean_box(i + 1);
    }
    if (c & 0xe0) == 0xc0 {
        return lean_box(i + 2);
    }
    if (c & 0xf0) == 0xe0 {
        return lean_box(i + 3);
    }
    if (c & 0xf8) == 0xf0 {
        return lean_box(i + 4);
    }
    lean_box(i + 1)
}
