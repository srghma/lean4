/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

unsafe extern "C" {
    fn lean_mk_ascii_string_unchecked(text: *const c_char) -> *mut LeanObject;
    fn lean_int_big_nonneg(value: *const LeanObject) -> bool;
}

fn lean_scalar_to_int(value: *mut LeanObject) -> c_int {
    unsafe { lean_unbox(value) as u32 as i32 }
}

fn float_to_string(text: String) -> *mut LeanObject {
    let cstr = std::ffi::CString::new(text).expect("float formatting produced embedded NUL");
    unsafe { lean_mk_ascii_string_unchecked(cstr.as_ptr()) }
}

unsafe fn lean_box_int(value: c_int) -> *mut LeanObject {
    lean_box(value as u32 as usize)
}

pub(crate) unsafe fn lean_box_float(value: f64) -> *mut LeanObject {
    // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 114 (🔁)

    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f64>() as c_uint);
    ptr::write_unaligned(
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f64,
        value,
    );
    obj
}

pub(crate) unsafe fn lean_box_float32(value: f32) -> *mut LeanObject {
    // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 128 (🔁)

    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f32>() as c_uint);
    ptr::write_unaligned(
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f32,
        value,
    );
    obj
}

unsafe fn lean_mk_float_exp_pair(
    float_value: *mut LeanObject,
    exp_value: *mut LeanObject,
) -> *mut LeanObject {
    let pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, float_value);
    lean_ctor_set(pair, 1, exp_value);
    pair
}

pub fn lean_float_to_string(value: f64) -> *mut LeanObject {
    if value.is_nan() {
        float_to_string("NaN".to_owned())
    } else {
        float_to_string(format!("{value:.6}"))
    }
}

pub unsafe fn lean_float_scaleb(value: f64, scale: *mut LeanObject) -> f64 {
    if lean_is_scalar(scale) {
        libm::scalbn(value, lean_scalar_to_int(scale))
    } else if value == 0.0 || !lean_int_big_nonneg(scale) {
        0.0
    } else {
        value * f64::INFINITY
    }
}

pub fn lean_float_isnan(value: f64) -> u8 {
    value.is_nan() as u8
}

pub fn lean_float_isfinite(value: f64) -> u8 {
    value.is_finite() as u8
}

pub fn lean_float_isinf(value: f64) -> u8 {
    value.is_infinite() as u8
}

pub fn lean_float_of_bits(bits: u64) -> f64 {
    let value = f64::from_bits(bits);
    if value.is_nan() { f64::NAN } else { value }
}

pub fn lean_float_to_bits(mut value: f64) -> u64 {
    if value.is_nan() {
        value = f64::NAN;
    }
    value.to_bits()
}

pub unsafe fn lean_float_frexp(value: f64) -> *mut LeanObject {
    let (significand, exponent) = libm::frexp(value);
    let exp_obj = if value.is_finite() {
        lean_box_int(exponent)
    } else {
        lean_box(0)
    };
    lean_mk_float_exp_pair(lean_box_float(significand), exp_obj)
}

pub fn lean_float32_to_string(value: f32) -> *mut LeanObject {
    if value.is_nan() {
        float_to_string("NaN".to_owned())
    } else {
        float_to_string(format!("{value:.6}"))
    }
}

pub unsafe fn lean_float32_scaleb(value: f32, scale: *mut LeanObject) -> f32 {
    if lean_is_scalar(scale) {
        libm::scalbnf(value, lean_scalar_to_int(scale))
    } else if value == 0.0 || !lean_int_big_nonneg(scale) {
        0.0
    } else {
        value * f32::INFINITY
    }
}

pub fn lean_float32_isnan(value: f32) -> u8 {
    value.is_nan() as u8
}

pub fn lean_float32_isfinite(value: f32) -> u8 {
    value.is_finite() as u8
}

pub fn lean_float32_isinf(value: f32) -> u8 {
    value.is_infinite() as u8
}

pub fn lean_float32_of_bits(bits: u32) -> f32 {
    let value = f32::from_bits(bits);
    if value.is_nan() { f32::NAN } else { value }
}

pub fn lean_float32_to_bits(mut value: f32) -> u32 {
    if value.is_nan() {
        value = f32::NAN;
    }
    value.to_bits()
}

pub unsafe fn lean_float32_frexp(value: f32) -> *mut LeanObject {
    let (significand, exponent) = libm::frexpf(value);
    let exp_obj = if value.is_finite() {
        lean_box_int(exponent)
    } else {
        lean_box(0)
    };
    lean_mk_float_exp_pair(lean_box_float32(significand), exp_obj)
}
