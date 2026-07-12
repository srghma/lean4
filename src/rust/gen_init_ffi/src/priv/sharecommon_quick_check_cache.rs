use leanh_l1::{datatypes::LeanObject, emitted::lean_inc::lean_inc};

use crate::r#priv::sharecommon_quick_data::{RustShareCommonQuick, ShareConsNode};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:19-39

pub(crate) unsafe fn sharecommon_quick_check_cache(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    if (*a).rc != 1 {
        if let Some(&cached) = this.cache.get(&(a as usize)) {
            let res = cached as *mut LeanObject;
            lean_inc(res);
            return res;
        }
        if this.check_set
            && let Some(node) = this.set.get(&ShareConsNode(a))
        {
            let res = node.0;
            lean_inc(res);
            return res;
        }
    }
    std::ptr::null_mut()
}
