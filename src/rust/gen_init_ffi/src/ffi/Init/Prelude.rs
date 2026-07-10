use leanh::LeanObject;
use leanh_l1::datatypes::{LeanObject,LeanScalarArray,LeanStringObject};
#[inline]
pub unsafe fn lean_uint8_of_nat_mk(n: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_uint8_of_nat_mk(n) }
}

// moved lean_uint8_to_nat to ffi/common/lean_uint8_to_nat__02__d5780543.rs
// original source: Init/Prelude.rs:9-11

#[inline]
pub unsafe fn lean_uint16_of_nat_mk(n: *mut LeanObject) -> u16 {
    unsafe { leanh::lean_uint16_of_nat_mk(n) }
}

// moved lean_uint16_to_nat to ffi/common/lean_uint16_to_nat__01__2f1608ce.rs, lean_uint16_to_nat__02__f78ff2a0.rs
// original source: Init/Prelude.rs:19-21

#[inline]
pub unsafe fn lean_uint32_of_nat_mk(n: *mut LeanObject) -> u32 {
    unsafe { leanh::lean_uint32_of_nat_mk(n) }
}

#[inline]
pub unsafe fn lean_uint32_to_nat(n: u32) -> *mut LeanObject {
    unsafe { leanh::lean_uint32_to_nat(n) }
}

#[inline]
pub unsafe fn lean_uint64_of_nat_mk(n: *mut LeanObject) -> u64 {
    unsafe { leanh::lean_uint64_of_nat_mk(n) }
}

// moved lean_uint64_to_nat to ffi/common/lean_uint64_to_nat__01__e7ac830a.rs, lean_uint64_to_nat__02__79d33bb4.rs
// original source: Init/Prelude.rs:38-40

#[inline]
pub unsafe fn lean_usize_of_nat_mk(n: *mut LeanObject) -> usize {
    unsafe { leanh::lean_usize_of_nat_mk(n) }
}

// moved lean_usize_to_nat to ffi/common/lean_usize_to_nat__01__5bddc13d.rs, lean_usize_to_nat__02__02764d04.rs
// original source: Init/Prelude.rs:46-48

#[inline]
pub unsafe fn lean_array_to_list(array: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_array_to_list(array) }
}

#[inline]
pub unsafe fn lean_array_mk(list: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_array_mk(list) }
}

#[inline]
pub unsafe fn lean_byte_array_mk(data: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_byte_array_mk(data) }
}

#[inline]
pub unsafe fn lean_byte_array_data(array: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_byte_array_data(array) }
}

// moved lean_string_to_utf8 to ffi/common/lean_string_to_utf8__02__a9d28cc5.rs
// original source: Init/Prelude.rs:74-76

#[inline]
pub unsafe fn lean_string_from_utf8_unchecked(bytes: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_string_from_utf8_unchecked(bytes) }
}

#[inline]
pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> u8 {
    leanh::lean_is_scalar(obj)
}

#[inline]
pub unsafe fn lean_sorry(synthetic: u8) -> *mut LeanObject {
    unsafe { leanh::lean_sorry(synthetic) }
}

#[inline]
pub unsafe fn lean_nat_add(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_add(a, b) }
}

#[inline]
pub unsafe fn lean_nat_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_mul(a, b) }
}

#[inline]
pub unsafe fn lean_nat_pow(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_pow(a, b) }
}

#[inline]
pub unsafe fn lean_nat_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_nat_dec_eq(a, b) }
}

#[inline]
pub unsafe fn lean_nat_dec_le(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_nat_dec_le(a, b) }
}

#[inline]
pub unsafe fn lean_nat_pred(a: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_pred(a) }
}

#[inline]
pub unsafe fn lean_nat_dec_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_nat_dec_lt(a, b) }
}

#[inline]
pub unsafe fn lean_nat_sub(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_sub(a, b) }
}

#[inline]
pub unsafe fn lean_nat_div(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_div(a, b) }
}

#[inline]
pub unsafe fn lean_nat_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_nat_mod(a, b) }
}

#[inline]
pub unsafe fn lean_system_platform_nbits(unit: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_system_platform_nbits(unit) }
}

#[inline]
pub unsafe fn lean_uint8_of_nat(n: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_uint8_of_nat(n) }
}

#[inline]
pub unsafe fn lean_uint8_dec_eq(a: u8, b: u8) -> u8 {
    unsafe { leanh::lean_uint8_dec_eq(a, b) }
}

#[inline]
pub unsafe fn lean_uint8_dec_lt(a: u8, b: u8) -> u8 {
    unsafe { leanh::lean_uint8_dec_lt(a, b) }
}

#[inline]
pub unsafe fn lean_uint8_dec_le(a: u8, b: u8) -> u8 {
    unsafe { leanh::lean_uint8_dec_le(a, b) }
}

// moved lean_uint16_of_nat to ffi/common/lean_uint16_of_nat__02__da248986.rs
// original source: Init/Prelude.rs:168-170

#[inline]
pub unsafe fn lean_uint16_dec_eq(a: u16, b: u16) -> u8 {
    unsafe { leanh::lean_uint16_dec_eq(a, b) }
}

// moved lean_uint32_of_nat to ffi/common/lean_uint32_of_nat__01__a2afd4e1.rs, lean_uint32_of_nat__02__438d38a2.rs
// original source: Init/Prelude.rs:176-178

#[inline]
pub unsafe fn lean_uint32_dec_eq(a: u32, b: u32) -> u8 {
    unsafe { leanh::lean_uint32_dec_eq(a, b) }
}

#[inline]
pub unsafe fn lean_uint32_dec_lt(a: u32, b: u32) -> u8 {
    unsafe { leanh::lean_uint32_dec_lt(a, b) }
}

#[inline]
pub unsafe fn lean_uint32_dec_le(a: u32, b: u32) -> u8 {
    unsafe { leanh::lean_uint32_dec_le(a, b) }
}

// moved lean_uint64_of_nat to ffi/common/lean_uint64_of_nat__01__2f57f70f.rs, lean_uint64_of_nat__02__321057a3.rs
// original source: Init/Prelude.rs:195-197

#[inline]
pub unsafe fn lean_uint64_dec_eq(a: u64, b: u64) -> u8 {
    unsafe { leanh::lean_uint64_dec_eq(a, b) }
}

// moved lean_usize_of_nat to ffi/common/lean_usize_of_nat__01__47af9c3b.rs, lean_usize_of_nat__02__bcd68a4e.rs, lean_usize_of_nat__03__47d65975.rs
// original source: Init/Prelude.rs:202-204

#[inline]
pub unsafe fn lean_usize_dec_eq(a: usize, b: usize) -> u8 {
    unsafe { leanh::lean_usize_dec_eq(a, b) }
}

#[inline]
pub unsafe fn lean_mk_empty_array_with_capacity(capacity: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_mk_empty_array_with_capacity(capacity) }
}

#[inline]
pub unsafe fn lean_array_get_size(array: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_array_get_size(array) }
}

#[inline]
pub unsafe fn lean_array_fget_borrowed(
    array: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_fget_borrowed(array, idx) }
}

#[inline]
pub unsafe fn lean_array_fget(array: *mut LeanObject, idx: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_array_fget(array, idx) }
}

#[inline]
pub unsafe fn lean_array_get_borrowed(
    default: *mut LeanObject,
    array: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_get_borrowed(default, array, idx) }
}

#[inline]
pub unsafe fn lean_array_get(
    default: *mut LeanObject,
    array: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_array_get(default, array, idx) }
}

#[inline]
pub unsafe fn lean_array_push(array: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_array_push(array, value) }
}

#[inline]
pub unsafe fn lean_mk_empty_byte_array(capacity: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_mk_empty_byte_array(capacity) }
}

#[inline]
pub unsafe fn lean_byte_array_push(array: *mut LeanObject, value: u8) -> *mut LeanObject {
    unsafe { leanh::lean_byte_array_push(array, value) }
}

#[inline]
pub unsafe fn lean_byte_array_size(array: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_byte_array_size(array) }
}

// moved lean_string_mk to ffi/common/lean_string_mk__02__4297187c.rs
// original source: Init/Prelude.rs:280-282

#[inline]
pub unsafe fn lean_string_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_string_dec_eq(a, b) }
}

#[inline]
pub unsafe fn lean_string_utf8_byte_size(s: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_string_utf8_byte_size(s) }
}

#[inline]
pub unsafe fn lean_panic_fn_borrowed(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { leanh::lean_panic_fn_borrowed(default_val, msg) }
}

#[inline]
pub fn lean_uint64_mix_hash(a: u64, b: u64) -> u64 {
    leanh::lean_uint64_mix_hash(a, b)
}

#[inline]
pub unsafe fn lean_string_hash(s: *mut LeanObject) -> u64 {
    unsafe { leanh::lean_string_hash(s) }
}

#[inline]
pub unsafe fn lean_name_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_name_eq(a, b) }
}
