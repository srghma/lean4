use crate::r#priv::lean_alloc_array::lean_alloc_array;
use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_inc::lean_inc,
        lean_is_scalar::lean_is_scalar,
    },
    r#priv::lean_array_cptr::lean_array_cptr,
};

#[inline]
pub unsafe fn lean_list_to_array(
    /*_: *mut LeanObject, */
    list: *mut LeanObject,
) -> *mut LeanObject {
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
