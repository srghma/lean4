// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:65-67
// exact-text variant: no

use crate::r#priv::{
    lean_char_default_value::lean_char_default_value, string_utf8_get_core::string_utf8_get_core,
};
use leanh_l1::r#priv::lean_string_size::lean_string_size;
use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_is_scalar::lean_is_scalar, lean_unbox::lean_unbox},
    r#priv::lean_string_cstr::lean_string_cstr,
};

pub unsafe fn lean_string_utf8_get(s: *const LeanObject, i0: *const LeanObject) -> u32 {
    if lean_is_scalar(i0) {
        let i = lean_unbox(i0);
        let str = lean_string_cstr(s) as *const u8;
        let size = lean_string_size(s) - 1;
        if i < size
            && let Some(cp) = string_utf8_get_core(str, size, i) {
                return cp;
            }
    }
    lean_char_default_value()
}
