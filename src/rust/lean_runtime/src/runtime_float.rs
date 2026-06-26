/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

extern "C" {
    fn lean_mk_ascii_string_unchecked(text: *const c_char) -> *mut LeanObject;
    fn lean_int_big_nonneg(value: *mut LeanObject) -> bool;
    #[link_name = "scalbn"]
    fn c_scalbn(value: f64, scale: c_int) -> f64;
    #[link_name = "scalbnf"]
    fn c_scalbnf(value: f32, scale: c_int) -> f32;
    #[link_name = "frexp"]
    fn c_frexp(value: f64, exp: *mut c_int) -> f64;
    #[link_name = "frexpf"]
    fn c_frexpf(value: f32, exp: *mut c_int) -> f32;
}

fn lean_scalar_to_int(value: *mut LeanObject) -> c_int {
    #[cfg(target_pointer_width = "64")]
    {
        unsafe { lean_unbox(value) as u32 as i32 }
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        (value as isize >> 1) as c_int
    }
}

pub(crate) fn float_to_string(text: String) -> *mut LeanObject {
    let cstr = std::ffi::CString::new(text).expect("float formatting produced embedded NUL");
    unsafe { lean_mk_ascii_string_unchecked(cstr.as_ptr()) }
}

pub(crate) unsafe fn lean_box_int(value: c_int) -> *mut LeanObject {
    lean_box(value as u32 as usize)
}

#[inline]
pub(crate) unsafe fn lean_box_float(value: f64) -> *mut LeanObject {
    let obj = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<f64>() as c_uint);
    ptr::write_unaligned(
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f64,
        value,
    );
    obj
}

#[inline]
pub(crate) unsafe fn lean_box_float32(value: f32) -> *mut LeanObject {
    let obj = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<f32>() as c_uint);
    ptr::write_unaligned(
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f32,
        value,
    );
    obj
}

#[inline]
pub(crate) unsafe fn lean_unbox_float(o: *mut LeanObject) -> f64 {
    lean_ctor_get_float(o, 0)
}

#[inline]
pub(crate) unsafe fn lean_unbox_float32(o: *mut LeanObject) -> f32 {
    lean_ctor_get_float32(o, 0)
}

#[inline]
pub(crate) fn lean_float_add(a: f64, b: f64) -> f64 {
    a + b
}

#[inline]
pub(crate) fn lean_float_sub(a: f64, b: f64) -> f64 {
    a - b
}

#[inline]
pub(crate) fn lean_float_mul(a: f64, b: f64) -> f64 {
    a * b
}

#[inline]
pub(crate) fn lean_float_div(a: f64, b: f64) -> f64 {
    a / b
}

#[inline]
pub(crate) fn lean_float_negate(a: f64) -> f64 {
    -a
}

#[inline]
pub(crate) fn lean_float_beq(a: f64, b: f64) -> u8 {
    (a == b) as u8
}

#[inline]
pub(crate) fn lean_float_decLe(a: f64, b: f64) -> u8 {
    (a <= b) as u8
}

#[inline]
pub(crate) fn lean_float_decLt(a: f64, b: f64) -> u8 {
    (a < b) as u8
}

#[inline]
pub(crate) fn lean_float32_add(a: f32, b: f32) -> f32 {
    a + b
}

#[inline]
pub(crate) fn lean_float32_sub(a: f32, b: f32) -> f32 {
    a - b
}

#[inline]
pub(crate) fn lean_float32_mul(a: f32, b: f32) -> f32 {
    a * b
}

#[inline]
pub(crate) fn lean_float32_div(a: f32, b: f32) -> f32 {
    a / b
}

#[inline]
pub(crate) fn lean_float32_negate(a: f32) -> f32 {
    -a
}

#[inline]
pub(crate) fn lean_float32_beq(a: f32, b: f32) -> u8 {
    (a == b) as u8
}

#[inline]
pub(crate) fn lean_float32_decLe(a: f32, b: f32) -> u8 {
    (a <= b) as u8
}

#[inline]
pub(crate) fn lean_float32_decLt(a: f32, b: f32) -> u8 {
    (a < b) as u8
}

pub(crate) unsafe fn lean_mk_float_exp_pair(
    float_value: *mut LeanObject,
    exp_value: *mut LeanObject,
) -> *mut LeanObject {
    let pair = lean_runtime_alloc_ctor(0, 2, 0);
    lean_runtime_ctor_set(pair, 0, float_value);
    lean_runtime_ctor_set(pair, 1, exp_value);
    pair
}

#[inline]
pub(crate) fn lean_float_to_string(value: f64) -> *mut LeanObject {
    if value.is_nan() {
        float_to_string("NaN".to_owned())
    } else {
        float_to_string(format!("{value:.6}"))
    }
}

#[inline]
pub(crate) unsafe fn lean_float_scaleb(value: f64, scale: *mut LeanObject) -> f64 {
    if lean_is_scalar(scale) {
        c_scalbn(value, lean_scalar_to_int(scale))
    } else if value == 0.0 || !lean_int_big_nonneg(scale) {
        0.0
    } else {
        value * f64::INFINITY
    }
}

#[inline]
pub(crate) fn lean_float_isnan(value: f64) -> u8 {
    value.is_nan() as u8
}

#[inline]
pub(crate) fn lean_float_isfinite(value: f64) -> u8 {
    value.is_finite() as u8
}

#[inline]
pub(crate) fn lean_float_isinf(value: f64) -> u8 {
    value.is_infinite() as u8
}

#[inline]
pub(crate) fn lean_float_of_bits(bits: u64) -> f64 {
    let value = f64::from_bits(bits);
    if value.is_nan() {
        f64::NAN
    } else {
        value
    }
}

#[inline]
pub(crate) fn lean_float_to_bits(mut value: f64) -> u64 {
    if value.is_nan() {
        value = f64::NAN;
    }
    value.to_bits()
}

#[inline]
pub(crate) unsafe fn lean_float_frexp(value: f64) -> *mut LeanObject {
    let mut exp = 0;
    let significand = c_frexp(value, &mut exp);
    let exp_obj = if value.is_finite() {
        lean_box_int(exp)
    } else {
        lean_box(0)
    };
    lean_mk_float_exp_pair(lean_box_float(significand), exp_obj)
}

#[inline]
pub(crate) fn lean_float32_to_string(value: f32) -> *mut LeanObject {
    if value.is_nan() {
        float_to_string("NaN".to_owned())
    } else {
        float_to_string(format!("{value:.6}"))
    }
}

#[inline]
pub(crate) unsafe fn lean_float32_scaleb(value: f32, scale: *mut LeanObject) -> f32 {
    if lean_is_scalar(scale) {
        c_scalbnf(value, lean_scalar_to_int(scale))
    } else if value == 0.0 || !lean_int_big_nonneg(scale) {
        0.0
    } else {
        value * f32::INFINITY
    }
}

#[inline]
pub(crate) fn lean_float32_isnan(value: f32) -> u8 {
    value.is_nan() as u8
}

#[inline]
pub(crate) fn lean_float32_isfinite(value: f32) -> u8 {
    value.is_finite() as u8
}

#[inline]
pub(crate) fn lean_float32_isinf(value: f32) -> u8 {
    value.is_infinite() as u8
}

#[inline]
pub(crate) fn lean_float32_of_bits(bits: u32) -> f32 {
    let value = f32::from_bits(bits);
    if value.is_nan() {
        f32::NAN
    } else {
        value
    }
}

#[inline]
pub(crate) fn lean_float32_to_bits(mut value: f32) -> u32 {
    if value.is_nan() {
        value = f32::NAN;
    }
    value.to_bits()
}

#[inline]
pub(crate) unsafe fn lean_float32_frexp(value: f32) -> *mut LeanObject {
    let mut exp = 0;
    let significand = c_frexpf(value, &mut exp);
    let exp_obj = if value.is_finite() {
        lean_box_int(exp)
    } else {
        lean_box(0)
    };
    lean_mk_float_exp_pair(lean_box_float32(significand), exp_obj)
}
