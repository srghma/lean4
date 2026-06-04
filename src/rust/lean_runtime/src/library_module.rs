// Port of src/library/module.cpp to Rust.
//
// module.cpp exports two LEAN_EXPORT extern "C" functions:
//   lean_compacted_region_save  — writes a .olean file
//   lean_compacted_region_read  — reads a .olean file
//
// Both functions are large (mmap, Windows handles, v2/v3 .olean format, lib
// relocation tables) and depend heavily on C++ types (object_compactor,
// compacted_region, sstream, etc.).  They stay in C++; Rust owns the exported
// symbols and delegates.

mod library_module_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_compacted_region_save(
            ofname: *mut LeanObject,
            module_name: *mut LeanObject,
            odata: *mut LeanObject,
            odep_regions: *mut LeanObject,
            oprev: *mut LeanObject,
            allow_closures: u8,
            w: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_cxx_compacted_region_read(
            ofname: *mut LeanObject,
            odep_regions: *mut LeanObject,
            w: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    /// `CompactedRegion.save (fname : @& String) (mod : @& Name) (data : α)
    ///    (depRegions : @& Array USize) (prev : Option CompactorHandle)
    ///    (allowClosures : Bool) : IO CompactorHandle`
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_save(
        ofname: *mut LeanObject,
        module_name: *mut LeanObject,
        odata: *mut LeanObject,
        odep_regions: *mut LeanObject,
        oprev: *mut LeanObject,
        allow_closures: u8,
        w: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_compacted_region_save(
            ofname,
            module_name,
            odata,
            odep_regions,
            oprev,
            allow_closures,
            w,
        )
    }

    /// `CompactedRegion.read (fname : @& String) (depRegions : @& Array USize) :
    ///    IO (α × USize)`
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_read(
        ofname: *mut LeanObject,
        odep_regions: *mut LeanObject,
        w: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_compacted_region_read(ofname, odep_regions, w)
    }
}
