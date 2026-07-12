use leanh_l1::datatypes::LeanObject;
use leanh_l1_initializers::r#priv::{
    lean_alloc_sarray::lean_alloc_sarray, lean_sarray_cptr::lean_sarray_cptr,
    lean_sarray_size::lean_sarray_size,
};

use crate::r#priv::{sharecommon_data::ShareCommonFn, sharecommon_fn_save::sharecommon_fn_save};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:75-84

pub(crate) unsafe fn sharecommon_fn_visit_sarray(this: &mut ShareCommonFn, a: *mut LeanObject) {
    let sz = lean_sarray_size(a);
    let other = (*a).other;
    let new_a = lean_alloc_sarray(other as u32, sz, sz);
    let dest = lean_sarray_cptr(new_a).cast_mut();
    let src = lean_sarray_cptr(a);
    libc::memcpy(dest.cast(), src.cast(), (other as usize) * sz);
    sharecommon_fn_save(this, a, new_a);
}
