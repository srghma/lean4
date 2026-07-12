use leanh_l1::{
    datatypes::LeanObject,
    emitted::lean_inc::lean_inc,
    r#priv::lean_array_size::lean_array_size,
};

use crate::{
    r#priv::{
        lean_array_get_core::lean_array_get_core,
        lean_alloc_array::lean_alloc_array, sharecommon_data::ShareCommonFn,
        sharecommon_fn_push_child::sharecommon_fn_push_child,
        sharecommon_fn_save::sharecommon_fn_save,
    },
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:75-96

pub unsafe fn sharecommon_fn_visit_array(this: &mut ShareCommonFn, a: *mut LeanObject) {
    this.children.clear();
    let mut missing_children = false;
    let sz = lean_array_size(a);
    for i in 0..sz {
        if !sharecommon_fn_push_child(this, lean_array_get_core(a, i)) {
            missing_children = true;
        }
    }
    if missing_children {
        return;
    }
    let new_a = lean_alloc_array(sz, sz);
    let array_data_ptr = (new_a as *mut u8).add(24) as *mut *mut LeanObject;
    for i in 0..sz {
        let child = this.children[i];
        lean_inc(child);
        array_data_ptr.add(i).write(child);
    }
    sharecommon_fn_save(this, a, new_a);
}
