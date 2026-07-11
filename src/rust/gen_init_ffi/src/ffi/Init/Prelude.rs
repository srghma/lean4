use std::ffi::c_char;

use leanh_l1::{
    datatypes::{LeanObject, LeanScalarArray, LeanStringObject},
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_box::lean_box, lean_ctor_get::lean_ctor_get,
        lean_ctor_set::lean_ctor_set, lean_dec::lean_dec, lean_inc::lean_inc,
        lean_unbox::lean_unbox,
    },
    r#priv::{
        lean_array_cptr::lean_array_cptr, lean_array_size::lean_array_size,
        lean_usize_to_nat::lean_usize_to_nat,
    },
    runtime_object_panic::lean_internal_panic_out_of_memory::{c_char_ptr, lean_internal_panic},
};
use leanh_l1_initializers::r#priv::{
    lean_alloc_sarray::lean_alloc_sarray, lean_sarray_cptr::lean_sarray_cptr,
    lean_sarray_size::lean_sarray_size,
};

pub use crate::r#priv::uint_family::lean_uint8_dec_eq;
pub use crate::r#priv::uint_family::lean_uint8_dec_le;
pub use crate::r#priv::uint_family::lean_uint8_dec_lt;
pub use crate::r#priv::uint_family::lean_uint8_of_nat;
pub use crate::r#priv::uint_family::lean_uint8_of_nat_mk;
use crate::{
    r#priv::lean_sarray_mut_cptr::lean_sarray_mut_cptr,
    todo_import_from_lean::lean_array_to_list_impl::lean_array_to_list_impl,
};
use crate::{
    r#priv::{
        lean_alloc_array::lean_alloc_array,
        lean_mk_string_from_bytes_unchecked::lean_mk_string_from_bytes_unchecked,
    },
    todo_import_from_lean::lean_list_to_array::lean_list_to_array,
};

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
    return lean_array_to_list_impl(/* lean_box(0), */ a);
}

#[inline]
pub unsafe fn lean_array_mk(list: *mut LeanObject) -> *mut LeanObject {
    return lean_list_to_array(/* lean_box(0), */ list);
}

#[inline]
pub unsafe fn lean_byte_array_mk(a: *mut LeanObject) -> *mut LeanObject {
    let sz = lean_array_size(a);
    let r = lean_alloc_sarray(1, sz, sz);
    let src = lean_array_cptr(a);
    let dst = lean_sarray_mut_cptr(r);
    for i in 0..sz {
        *dst.add(i) = lean_unbox(*src.add(i)) as u8;
    }
    lean_dec(a);
    r
}

#[inline]
pub unsafe fn lean_byte_array_data(a: *mut LeanObject) -> *mut LeanObject {
    let sz = lean_sarray_size(a);
    let r = lean_alloc_array(sz, sz);
    let src = lean_sarray_cptr(a);
    let dst = lean_array_cptr(r);
    for i in 0..sz {
        *dst.add(i) = lean_box(*src.add(i) as usize);
    }
    lean_dec(a);
    r
}

// moved lean_string_to_utf8 to ffi/common/lean_string_to_utf8.rs
// original source: Init/Prelude.rs:74-76

#[inline]
pub unsafe fn lean_string_from_utf8_unchecked(bytes: *mut LeanObject) -> *mut LeanObject {
    let r = lean_mk_string_from_bytes_unchecked(
        lean_sarray_cptr(bytes) as *const c_char,
        lean_sarray_size(bytes),
    );
    lean_dec(bytes);
    r
}

pub use leanh_l1::emitted::lean_is_scalar::lean_is_scalar;

#[inline]
// TODO: what is _ ? remove
pub unsafe fn lean_sorry(_: u8) -> ! {
    lean_internal_panic(c_char_ptr(b"executed 'sorry'\0"))
}

pub use leanh_l1::runtime_object_nat_int::lean_nat_add;
pub use leanh_l1::runtime_object_nat_int::lean_nat_dec_eq;
pub use leanh_l1::runtime_object_nat_int::lean_nat_dec_le;
pub use leanh_l1::runtime_object_nat_int::lean_nat_dec_lt;
pub use leanh_l1::runtime_object_nat_int::lean_nat_div;
pub use leanh_l1::runtime_object_nat_int::lean_nat_mod;
pub use leanh_l1::runtime_object_nat_int::lean_nat_mul;
pub use leanh_l1::runtime_object_nat_int::lean_nat_pow;
pub use leanh_l1::runtime_object_nat_int::lean_nat_pred;
pub use leanh_l1::runtime_object_nat_int::lean_nat_to_int;
pub use leanh_l1::runtime_object_nat_int::lean_nat_sub;

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

pub use leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash;

#[inline]
pub unsafe fn lean_string_hash(s: *mut LeanObject) -> u64 {
    unsafe { leanh::lean_string_hash(s) }
}

#[inline]
pub unsafe fn lean_name_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe { leanh::lean_name_eq(a, b) }
}
