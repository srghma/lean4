use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_box::lean_box, lean_ctor_set::lean_ctor_set,
        lean_dec::lean_dec, lean_inc::lean_inc,
    },
    r#priv::{lean_array_cptr::lean_array_cptr, lean_array_size::lean_array_size},
};

#[inline]
pub unsafe fn lean_array_to_list_impl(
    /*_: *mut LeanObject, */
    a: *mut LeanObject,
) -> *mut LeanObject {
    let mut i = lean_array_size(a);
    let mut r = lean_box(0);
    while i > 0 {
        i -= 1;
        let v = *lean_array_cptr(a).add(i);
        let cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, v);
        lean_inc(v);
        lean_ctor_set(cell, 1, r);
        r = cell;
    }
    lean_dec(a);
    r
}
