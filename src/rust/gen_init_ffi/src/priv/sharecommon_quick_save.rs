use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_dec::lean_dec, lean_inc::lean_inc},
};

use crate::r#priv::sharecommon_quick_data::{RustShareCommonQuick, ShareConsNode};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:40-60

pub(crate) unsafe fn sharecommon_quick_save(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
    new_a: *mut LeanObject,
) -> *mut LeanObject {
    let node = ShareConsNode(new_a);
    let result = if let Some(existing) = this.set.get(&node) {
        let res = existing.0;
        lean_dec(new_a);
        lean_inc(res);
        res
    } else {
        this.set.insert(node);
        new_a
    };
    if (*a).rc != 1 {
        this.cache.insert(a as usize, result as usize);
    }
    result
}
