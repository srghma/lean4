use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_dec::lean_dec, lean_inc::lean_inc, lean_is_exclusive::lean_is_exclusive},
    r#priv::{
        lean_array_capacity::lean_array_capacity, lean_array_cptr::lean_array_cptr,
        lean_array_size::lean_array_size, lean_free_object::lean_free_object,
    },
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic_out_of_memory,
};

use crate::r#priv::lean_alloc_array::lean_alloc_array;

pub unsafe fn lean_copy_expand_array(a: *mut LeanObject, expand: bool) -> *mut LeanObject {
    let sz = lean_array_size(a);
    let mut cap = lean_array_capacity(a);
    debug_assert!(cap >= sz);
    if expand {
        cap = cap
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .unwrap_or_else(|| lean_internal_panic_out_of_memory());
        debug_assert!(cap > sz);
    }
    let r = lean_alloc_array(sz, cap);
    let src = lean_array_cptr(a);
    let dst = lean_array_cptr(r);
    if lean_is_exclusive(a) {
        core::ptr::copy_nonoverlapping(src, dst, sz);
        lean_free_object(a);
    } else {
        for i in 0..sz {
            let value = *src.add(i);
            *dst.add(i) = value;
            lean_inc(value);
        }
        lean_dec(a);
    }
    r
}
