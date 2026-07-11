use leanh_l1::{
    datatypes::LeanObject, emitted::lean_dec::lean_dec,
    r#priv::lean_sarray_elem_size::lean_sarray_elem_size,
};
use leanh_l1_initializers::r#priv::{
    lean_alloc_sarray::lean_alloc_sarray, lean_sarray_cptr::lean_sarray_cptr,
    lean_sarray_size::lean_sarray_size,
};

use crate::r#priv::lean_sarray_mut_cptr::lean_sarray_mut_cptr;

#[inline]
pub unsafe fn lean_copy_sarray(a: *mut LeanObject, cap: usize) -> *mut LeanObject {
    let esz = lean_sarray_elem_size(a);
    let sz = lean_sarray_size(a);
    debug_assert!(cap >= sz);
    let r = lean_alloc_sarray(esz as u32, sz, cap);
    core::ptr::copy_nonoverlapping(lean_sarray_cptr(a), lean_sarray_mut_cptr(r), esz * sz);
    lean_dec(a);
    r
}
