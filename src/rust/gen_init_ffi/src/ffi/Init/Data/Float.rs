use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};

// Generated stub file for Lean FFI imports
// Source: src/Init/Data/Float.lean

pub fn lean_float_add(a: f64, b: f64) -> f64 {
    a + b
}

pub fn lean_float_sub(a: f64, b: f64) -> f64 {
    a - b
}

pub fn lean_float_mul(a: f64, b: f64) -> f64 {
    a * b
}

pub fn lean_float_div(a: f64, b: f64) -> f64 {
    a / b
}

pub fn lean_float_negate(a: f64) -> f64 {
    -a
}

pub fn lean_float_of_bits(bits: u64) -> f64 {
    f64::from_bits(bits)
}

pub fn lean_float_to_bits(value: f64) -> u64 {
    value.to_bits()
}

pub fn lean_float_beq(a: f64, b: f64) -> bool {
    a == b
}

pub fn lean_float_decLt(a: f64, b: f64) -> bool {
    a < b
}

pub fn lean_float_decLe(a: f64, b: f64) -> bool {
    a <= b
}

pub unsafe fn lean_float_to_string(value: f64) -> *mut LeanObject {
    let text = std::ffi::CString::new(value.to_string()).unwrap();
    unsafe { lean_mk_string(text.as_ptr()) }
}

pub fn lean_float_to_uint8(value: f64) -> u8 {
    value as u8
}

pub fn lean_float_to_uint16(value: f64) -> u16 {
    value as u16
}

pub fn lean_float_to_uint32(value: f64) -> u32 {
    value as u32
}

pub fn lean_float_to_uint64(value: f64) -> u64 {
    value as u64
}

pub fn lean_float_to_usize(value: f64) -> usize {
    value as usize
}

pub fn lean_float_isnan(value: f64) -> bool {
    value.is_nan()
}

pub fn lean_float_isfinite(value: f64) -> bool {
    value.is_finite()
}

pub fn lean_float_isinf(value: f64) -> bool {
    value.is_infinite()
}

pub fn lean_float_frexp(_: f64) -> *mut LeanObject {
    todo!("Stub for lean_float_frexp");
}

pub fn lean_uint8_to_float(value: u8) -> f64 {
    value as f64
}

pub fn lean_uint16_to_float(value: u16) -> f64 {
    value as f64
}

pub fn lean_uint32_to_float(value: u32) -> f64 {
    value as f64
}

pub fn lean_uint64_to_float(value: u64) -> f64 {
    value as f64
}

pub fn lean_usize_to_float(value: usize) -> f64 {
    value as f64
}

pub fn sin(value: f64) -> f64 {
    value.sin()
}

pub fn cos(value: f64) -> f64 {
    value.cos()
}

pub fn tan(value: f64) -> f64 {
    value.tan()
}

pub fn asin(value: f64) -> f64 {
    value.asin()
}

pub fn acos(value: f64) -> f64 {
    value.acos()
}

pub fn atan(value: f64) -> f64 {
    value.atan()
}

pub fn atan2(y: f64, x: f64) -> f64 {
    y.atan2(x)
}

pub fn sinh(value: f64) -> f64 {
    value.sinh()
}

pub fn cosh(value: f64) -> f64 {
    value.cosh()
}

pub fn tanh(value: f64) -> f64 {
    value.tanh()
}

pub fn asinh(value: f64) -> f64 {
    value.asinh()
}

pub fn acosh(value: f64) -> f64 {
    value.acosh()
}

pub fn atanh(value: f64) -> f64 {
    value.atanh()
}

pub fn exp(value: f64) -> f64 {
    value.exp()
}

pub fn exp2(value: f64) -> f64 {
    value.exp2()
}

pub fn log(value: f64) -> f64 {
    value.ln()
}

pub fn log2(value: f64) -> f64 {
    value.log2()
}

pub fn log10(value: f64) -> f64 {
    value.log10()
}

pub fn pow(value: f64, exp: f64) -> f64 {
    value.powf(exp)
}

pub fn sqrt(value: f64) -> f64 {
    value.sqrt()
}

pub fn cbrt(value: f64) -> f64 {
    value.cbrt()
}

pub fn ceil(value: f64) -> f64 {
    value.ceil()
}

pub fn floor(value: f64) -> f64 {
    value.floor()
}

pub fn round(value: f64) -> f64 {
    value.round()
}

pub fn fabs(value: f64) -> f64 {
    value.abs()
}

pub unsafe fn lean_float_scaleb(value: f64, exp: *mut LeanObject) -> f64 {
    value * 2.0f64.powi(unsafe { lean_unbox(exp) } as i32)
}
