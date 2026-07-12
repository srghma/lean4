use leanh_l1::{
    datatypes::LeanObject,
    r#priv::lean_array_size::lean_array_size,
};

use crate::{
    r#priv::{
        lean_array_get_core::lean_array_get_core,
        lean_alloc_array::lean_alloc_array,
        sharecommon_quick_check_cache::sharecommon_quick_check_cache,
        sharecommon_quick_data::RustShareCommonQuick,
        sharecommon_quick_save::sharecommon_quick_save,
        sharecommon_quick_visit::sharecommon_quick_visit,
    },
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:76-93

pub(crate) unsafe fn sharecommon_quick_visit_array(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let r = sharecommon_quick_check_cache(this, a);
    if !r.is_null() {
        return r;
    }
    let sz = lean_array_size(a);
    let new_a = lean_alloc_array(sz, sz);
    let array_data_ptr = (new_a as *mut u8).add(24) as *mut *mut LeanObject;
    for i in 0..sz {
        let child = sharecommon_quick_visit(this, lean_array_get_core(a, i));
        array_data_ptr.add(i).write(child);
    }
    sharecommon_quick_save(this, a, new_a)
}
