/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_level_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_level_mk_data(
            h: u64,
            depth: *mut LeanObject,
            hasMVar: u8,
            hasParam: u8,
        ) -> u64;
        fn lean_cxx_level_eqv(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
        fn lean_cxx_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_level_mk_data(
        h: u64,
        depth: *mut LeanObject,
        hasMVar: u8,
        hasParam: u8,
    ) -> u64 {
        lean_cxx_level_mk_data(h, depth, hasMVar, hasParam)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_level_eqv(l1: *mut LeanObject, l2: *mut LeanObject) -> u8 {
        lean_cxx_level_eqv(l1, l2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8 {
        lean_cxx_level_eq(l1, l2)
    }
}
