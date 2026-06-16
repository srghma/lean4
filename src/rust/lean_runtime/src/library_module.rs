/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_module_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_compacted_region_save(
            ofname: *mut LeanObject,
            mod_: *mut LeanObject,
            odata: *mut LeanObject,
            odep_regions: *mut LeanObject,
            oprev: *mut LeanObject,
            allow_closures: u8,
            io: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_compacted_region_read(
            ofname: *mut LeanObject,
            odep_regions: *mut LeanObject,
            io: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_save(
        ofname: *mut LeanObject,
        mod_: *mut LeanObject,
        odata: *mut LeanObject,
        odep_regions: *mut LeanObject,
        oprev: *mut LeanObject,
        allow_closures: u8,
        io: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_compacted_region_save(ofname, mod_, odata, odep_regions, oprev, allow_closures, io)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_read(
        ofname: *mut LeanObject,
        odep_regions: *mut LeanObject,
        io: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_compacted_region_read(ofname, odep_regions, io)
    }
}
