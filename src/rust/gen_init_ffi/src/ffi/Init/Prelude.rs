use std::ffi::c_char;

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_box::lean_box, lean_dec::lean_dec, lean_inc::lean_inc,
        lean_is_exclusive::lean_is_exclusive, lean_unbox::lean_unbox,
    },
    r#priv::{
        lean_array_capacity::lean_array_capacity, lean_array_cptr::lean_array_cptr,
        lean_array_size::lean_array_size, lean_string_size::lean_string_size,
    },
    runtime_object_panic::lean_internal_panic_out_of_memory::{
        lean_internal_panic, lean_internal_panic_out_of_memory,
    },
};
use leanh_l1_initializers::r#priv::{
    lean_alloc_sarray::lean_alloc_sarray, lean_sarray_cptr::lean_sarray_cptr,
    lean_sarray_set_size::lean_sarray_set_size, lean_sarray_size::lean_sarray_size,
};

pub use leanh_l1::emitted::lean_is_scalar::lean_is_scalar;

pub use crate::r#priv::uint_family::lean_uint16_dec_eq;
pub use crate::r#priv::uint_family::lean_uint16_of_nat;
pub use crate::r#priv::uint_family::lean_uint16_of_nat_mk;
pub use crate::r#priv::uint_family::lean_uint16_to_nat;
pub use crate::r#priv::uint_family::lean_uint32_dec_eq;
pub use crate::r#priv::uint_family::lean_uint32_dec_le;
pub use crate::r#priv::uint_family::lean_uint32_dec_lt;
pub use crate::r#priv::uint_family::lean_uint32_of_nat;
pub use crate::r#priv::uint_family::lean_uint32_of_nat_mk;
pub use crate::r#priv::uint_family::lean_uint32_to_nat;
pub use crate::r#priv::uint_family::lean_uint64_dec_eq;
pub use crate::r#priv::uint_family::lean_uint64_of_nat;
pub use crate::r#priv::uint_family::lean_uint64_of_nat_mk;
pub use crate::r#priv::uint_family::lean_uint64_to_nat;
pub use crate::r#priv::uint_family::lean_uint8_dec_eq;
pub use crate::r#priv::uint_family::lean_uint8_dec_le;
pub use crate::r#priv::uint_family::lean_uint8_dec_lt;
pub use crate::r#priv::uint_family::lean_uint8_of_nat;
pub use crate::r#priv::uint_family::lean_uint8_of_nat_mk;
pub use crate::r#priv::uint_family::lean_uint8_to_nat;
pub use crate::r#priv::uint_family::lean_usize_dec_eq;
pub use crate::r#priv::uint_family::lean_usize_of_nat;
pub use crate::r#priv::uint_family::lean_usize_of_nat_mk;
pub use crate::r#priv::uint_family::lean_usize_to_nat;
use crate::{
    r#priv::{
        lean_alloc_array::lean_alloc_array, lean_array_get_panic::lean_array_get_panic,
        lean_array_set_size::lean_array_set_size, lean_copy_expand_array::lean_copy_expand_array,
        lean_copy_expand_array_nonlinear::lean_copy_expand_array_nonlinear,
        lean_mk_string_from_bytes_unchecked::lean_mk_string_from_bytes_unchecked,
        lean_panic_fn::lean_panic_fn, lean_sarray_ensure_capacity::lean_sarray_ensure_capacity,
        lean_sarray_ensure_exclusive::lean_sarray_ensure_exclusive,
        lean_sarray_mut_cptr::lean_sarray_mut_cptr,
    },
    todo_import_from_lean::lean_array_to_list_impl::lean_array_to_list_impl,
    todo_import_from_lean::lean_list_to_array::lean_list_to_array,
};

pub use leanh_l1_initializers::todo_import_from_lean::lean_name_mk_string::lean_string_hash;

#[inline]
unsafe fn lean_array_get_core(a: *mut LeanObject, idx: usize) -> *mut LeanObject {
    *lean_array_cptr(a).add(idx)
}

#[inline]
unsafe fn lean_array_uget(a: *mut LeanObject, idx: usize) -> *mut LeanObject {
    let r = lean_array_get_core(a, idx);
    lean_inc(r);
    r
}

// moved lean_uint8_to_nat to ffi/common/lean_uint8_to_nat.rs
// original source: Init/Prelude.rs:9-11

// moved lean_uint16_to_nat to ffi/common/lean_uint16_to_nat.rs
// original source: Init/Prelude.rs:19-21

// moved lean_uint64_to_nat to ffi/common/lean_uint64_to_nat.rs
// original source: Init/Prelude.rs:38-40

// moved lean_usize_to_nat to ffi/common/lean_usize_to_nat.rs
// original source: Init/Prelude.rs:46-48

#[inline]
pub unsafe fn lean_array_to_list(a: *mut LeanObject) -> *mut LeanObject {
    lean_array_to_list_impl(/* lean_box(0), */ a)
}

#[inline]
pub unsafe fn lean_array_mk(list: *mut LeanObject) -> *mut LeanObject {
    lean_list_to_array(/* lean_box(0), */ list)
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
        lean_sarray_cptr(bytes).cast::<c_char>(),
        lean_sarray_size(bytes),
    );
    lean_dec(bytes);
    r
}

#[inline]
// TODO: what is _ ? remove
pub unsafe fn lean_sorry(_: u8) -> ! {
    lean_internal_panic("executed 'sorry'")
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
pub use leanh_l1::runtime_object_nat_int::lean_nat_sub;

#[inline]
pub unsafe fn lean_system_platform_nbits(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(core::mem::size_of::<*const u8>() * 8)
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
    if !lean_is_scalar(capacity) {
        lean_internal_panic_out_of_memory();
    }
    lean_alloc_array(0, lean_unbox(capacity))
}

#[inline]
pub unsafe fn lean_array_get_size(array: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_array_size(array))
}

#[inline]
pub unsafe fn lean_array_fget_borrowed(
    array: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    lean_array_get_core(array, lean_unbox(idx))
}

#[inline]
pub unsafe fn lean_array_fget(array: *mut LeanObject, idx: *mut LeanObject) -> *mut LeanObject {
    lean_array_uget(array, lean_unbox(idx))
}

#[inline]
pub unsafe fn lean_array_get_borrowed(
    default: *mut LeanObject,
    array: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_scalar(idx) {
        let idx = lean_unbox(idx);
        if idx < lean_array_size(array) {
            return lean_array_get_core(array, idx);
        }
    }
    /* Recall that if `i` is not a scalar, then it must be out of bounds because
    i > LEAN_MAX_SMALL_NAT == MAX_UNSIGNED >> 1
    but each array entry is 8 bytes in 64-bit machines and 4 in 32-bit ones.
    In both cases, we would be out-of-memory. */
    lean_inc(default);
    lean_array_get_panic(default)
}

#[inline]
pub unsafe fn lean_array_get(
    default: *mut LeanObject,
    array: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_scalar(idx) {
        let idx = lean_unbox(idx);
        if idx < lean_array_size(array) {
            return lean_array_uget(array, idx);
        }
    }
    /* Recall that if `i` is not a scalar, then it must be out of bounds because
    i > LEAN_MAX_SMALL_NAT == MAX_UNSIGNED >> 1
    but each array entry is 8 bytes in 64-bit machines and 4 in 32-bit ones.
    In both cases, we would be out-of-memory. */
    lean_inc(default);
    lean_array_get_panic(default)
}

#[inline]
pub unsafe fn lean_array_push(array: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
    let r = if lean_is_exclusive(array) {
        if lean_array_capacity(array) > lean_array_size(array) {
            array
        } else {
            lean_copy_expand_array(array, true)
        }
    } else {
        lean_copy_expand_array_nonlinear(
            array,
            lean_array_capacity(array) < 2 * lean_array_size(array) + 1,
        )
    };
    debug_assert!(lean_array_capacity(r) > lean_array_size(r));
    let sz = lean_array_size(r);
    *lean_array_cptr(r).add(sz) = value;
    lean_array_set_size(r, sz + 1);
    r
}

#[inline]
pub unsafe fn lean_mk_empty_byte_array(capacity: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(capacity) {
        lean_internal_panic_out_of_memory();
    }
    lean_alloc_sarray(1, 0, lean_unbox(capacity))
}

#[inline]
pub unsafe fn lean_byte_array_push(array: *mut LeanObject, value: u8) -> *mut LeanObject {
    let r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(
        array,
        lean_sarray_size(array) + 1,
        false,
    ));
    let sz = lean_sarray_size(r);
    *lean_sarray_mut_cptr(r).add(sz) = value;
    lean_sarray_set_size(r, sz + 1);
    r
}

#[inline]
pub unsafe fn lean_byte_array_size(array: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_sarray_size(array))
}

// moved lean_string_mk to ffi/common/lean_string_mk.rs
// original source: Init/Prelude.rs:280-282

pub use leanh_l1_initializers::runtime_object_name::lean_string_eq::lean_string_eq as lean_string_dec_eq;

#[inline]
pub unsafe fn lean_string_utf8_byte_size(s: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_string_size(s) - 1)
}

#[inline]
pub unsafe fn lean_panic_fn_borrowed(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(default_val);
    lean_panic_fn(default_val, msg)
}

pub use leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash;
pub use leanh_l1_initializers::kernel_type_checker::lean_name_eq::lean_name_eq;
