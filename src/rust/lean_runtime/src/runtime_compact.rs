/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod runtime_compact_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_compacted_region_is_memory_mapped(region: usize) -> u8;
        fn lean_cxx_compacted_region_size(region: usize) -> usize;
        fn lean_cxx_compacted_region_free(region: usize, io: *mut LeanObject) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_is_memory_mapped(region: usize) -> u8 {
        lean_cxx_compacted_region_is_memory_mapped(region)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_size(region: usize) -> usize {
        lean_cxx_compacted_region_size(region)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_free(
        region: usize,
        io: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_compacted_region_free(region, io)
    }
}
