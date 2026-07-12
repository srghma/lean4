use leanh_l1::{
    datatypes::LeanObject,
    emitted::lean_inc::lean_inc,
};

use crate::r#priv::sharecommon_quick_data::{RustShareCommonQuick, ShareConsNode};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:61-75

pub(crate) unsafe fn sharecommon_quick_visit_terminal(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let node = ShareConsNode(a);
    let res = if let Some(existing) = this.set.get(&node) {
        existing.0
    } else {
        this.set.insert(node);
        a
    };
    lean_inc(res);
    res
}
