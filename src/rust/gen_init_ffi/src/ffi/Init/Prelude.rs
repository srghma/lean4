use leanh_l1::{
    datatypes::{LEAN_MAX_SMALL_NAT, LeanObject, LeanScalarArray, LeanStringObject},
    emitted::{
        lean_box::lean_box, lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_inc::lean_inc,
        lean_unbox::lean_unbox,
    },
    r#priv::{
        lean_array_cptr::lean_array_cptr, lean_array_size::lean_array_size,
        lean_usize_to_nat::lean_usize_to_nat,
    },
    runtime_object_nat_int::{
        lean_nat_big_add, lean_nat_big_div, lean_nat_big_mod, lean_nat_big_mul, lean_nat_big_sub,
        lean_nat_overflow_mul,
    },
};

use crate::r#priv::lean_alloc_array::lean_alloc_array;
pub use crate::r#priv::uint_family::lean_uint8_dec_eq;
pub use crate::r#priv::uint_family::lean_uint8_dec_le;
pub use crate::r#priv::uint_family::lean_uint8_dec_lt;
pub use crate::r#priv::uint_family::lean_uint8_of_nat;
pub use crate::r#priv::uint_family::lean_uint8_of_nat_mk;

// moved lean_uint8_to_nat to ffi/common/lean_uint8_to_nat.rs
// original source: Init/Prelude.rs:9-11

pub use crate::r#priv::uint_family::lean_uint16_dec_eq;
pub use crate::r#priv::uint_family::lean_uint16_of_nat_mk;

// moved lean_uint16_to_nat to ffi/common/lean_uint16_to_nat.rs
// original source: Init/Prelude.rs:19-21

pub use crate::r#priv::uint_family::lean_uint32_dec_eq;
pub use crate::r#priv::uint_family::lean_uint32_dec_le;
pub use crate::r#priv::uint_family::lean_uint32_dec_lt;
pub use crate::r#priv::uint_family::lean_uint32_of_nat_mk;
pub use crate::r#priv::uint_family::lean_uint32_to_nat;
pub use crate::r#priv::uint_family::lean_uint64_dec_eq;
pub use crate::r#priv::uint_family::lean_uint64_of_nat_mk;
pub use crate::r#priv::uint_family::lean_usize_dec_eq;
pub use crate::r#priv::uint_family::lean_usize_of_nat_mk;

// moved lean_uint64_to_nat to ffi/common/lean_uint64_to_nat.rs
// original source: Init/Prelude.rs:38-40

// moved lean_usize_to_nat to ffi/common/lean_usize_to_nat.rs
// original source: Init/Prelude.rs:46-48

#[inline]
pub unsafe fn lean_array_to_list(a: *mut LeanObject) -> *mut LeanObject {
    // TODO: should use toListImpl / lean_array_to_list_impl
    let mut i = lean_array_size(a);
    let mut r = lean_box(0);
    while i > 0 {
        i -= 1;
        let v = *lean_array_cptr(a).add(i);
        let cell = lean_runtime_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, v);
        lean_inc(v);
        lean_ctor_set(cell, 1, r);
        r = cell;
    }
    lean_dec(a);
    r
}

#[inline]
pub unsafe fn lean_array_mk(list: *mut LeanObject) -> *mut LeanObject {
    // TODO: should use List.toArrayImpl / lean_list_to_array
    let mut sz = 0usize;
    let mut it = list;
    while !lean_is_scalar(it) {
        sz += 1;
        it = lean_ctor_get(it, 1);
    }
    let r = lean_alloc_array(sz, sz);
    let mut it = list;
    let dst = lean_array_cptr(r);
    for i in 0..sz {
        let v = lean_ctor_get(it, 0);
        *dst.add(i) = v;
        lean_inc(v);
        it = lean_ctor_get(it, 1);
    }
    lean_dec(list);
    r
}

#[inline]
pub unsafe fn lean_byte_array_mk(data: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_byte_array_mk(data) }
}

#[inline]
pub unsafe fn lean_byte_array_data(array: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_byte_array_data(array) }
}

// moved lean_string_to_utf8 to ffi/common/lean_string_to_utf8.rs
// original source: Init/Prelude.rs:74-76

#[inline]
pub unsafe fn lean_string_from_utf8_unchecked(bytes: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_string_from_utf8_unchecked(bytes) }
}

pub use leanh_l1::emitted::lean_is_scalar::lean_is_scalar;

#[inline]
pub unsafe fn lean_sorry(synthetic: u8) -> *mut LeanObject {
    unsafe { leanh::lean_sorry(synthetic) }
}

#[inline]
pub unsafe fn lean_nat_add(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        lean_usize_to_nat(lean_unbox(a1).wrapping_add(lean_unbox(a2)))
    } else {
        lean_nat_big_add(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        if n1 == 0 {
            return a;
        }
        let n2 = lean_unbox(b as *const _);
        let r = n1.wrapping_mul(n2);
        if r <= LEAN_MAX_SMALL_NAT && r / n1 == n2 {
            lean_box(r)
        } else {
            lean_nat_overflow_mul(n1, n2)
        }
    } else {
        lean_nat_big_mul(a, b)
    }
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
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        let n2 = lean_unbox(b as *const _);
        lean_box(if n1 >= n2 { n1 - n2 } else { 0 })
    } else {
        lean_nat_big_sub(a, b)
    }
}

#[inline]
pub unsafe fn lean_nat_div(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        let n2 = lean_unbox(b as *const _);
        lean_box(if n2 == 0 { 0 } else { n1 / n2 })
    } else {
        lean_nat_big_div(a, b)
    }
}

#[inline]
pub unsafe fn lean_nat_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        let n2 = lean_unbox(b as *const _);
        lean_box(if n2 == 0 { n1 } else { n1 % n2 })
    } else {
        lean_nat_big_mod(a, b)
    }
}

#[inline]
pub unsafe fn lean_system_platform_nbits(unit: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_system_platform_nbits(unit) }
}

// moved lean_uint16_of_nat to ffi/common/lean_uint16_of_nat.rs
// original source: Init/Prelude.rs:168-170

// moved lean_uint32_of_nat to ffi/common/lean_uint32_of_nat.rs
// original source: Init/Prelude.rs:176-178

// moved lean_uint64_of_nat to ffi/common/lean_uint64_of_nat.rs
// original source: Init/Prelude.rs:195-197

// moved lean_usize_of_nat to ffi/common/lean_usize_of_nat.rs
// original source: Init/Prelude.rs:202-204

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

// moved lean_string_mk to ffi/common/lean_string_mk.rs
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
