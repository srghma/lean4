use crate::r#priv::sharecommon_quick_data::{RustShareCommonQuick, ShareCache, ShareSet};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:65-72

pub(crate) fn sharecommon_quick_new(check_set: bool) -> RustShareCommonQuick {
    RustShareCommonQuick {
        cache: ShareCache::default(),
        set: ShareSet::default(),
        check_set,
    }
}
