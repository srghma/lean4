// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:65-67
// exact-text variant: no

use crate::ffi::Init::Data::String::Basic::lean_string_utf8_get_fast;
use leanh_l1::{
    datatypes::{LeanObject, LeanScalarArray, LeanStringObject},
    emitted::{lean_is_scalar::lean_is_scalar, lean_unbox::lean_unbox},
    r#priv::lean_string_cstr::lean_string_cstr,
};
use leanh_l1_initializers::r#priv::lean_string_size::lean_string_size;

pub unsafe fn lean_string_utf8_get(s: *const LeanObject, pos: *const LeanObject) -> u32 {
    if lean_is_scalar(i0) {
        let i = lean_unbox(i0);
        let str = lean_string_cstr(s) as *const u8;
        let size = lean_string_size(s) - 1;
        if i < size {
            if let Some(cp) = string_utf8_get_core(str, size, i) {
                return cp;
            }
        }
    }
    lean_char_default_value()
}
