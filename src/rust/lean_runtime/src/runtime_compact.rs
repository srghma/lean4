// runtime_compact.rs — port of runtime/compact.cpp
// Ported to Rust. Uses extern "C" shims for the C++ std::unordered_set,
// std::vector, and mmap/dlopen APIs that are platform-specific.
// The object_compactor and compacted_region types are exported as opaque
// pointers since they own C++ heap state through the shim layer.
//
// Integration: add `include!("runtime_compact.rs");` in lib.rs after
// the other runtime includes. Remove compact.cpp from CMakeLists RUNTIME_OBJS
// once compact_shims.cpp is added.

mod runtime_compact_impl {
    use super::*;
    use core::ffi::{c_char, c_int, c_void};
    use core::ptr::null_mut;

    // ---------------------------------------------------------------------------
    // FFI shims implemented in compact_shims.cpp
    // ---------------------------------------------------------------------------
    extern "C" {
        // object_compactor lifecycle
        fn lean_compact_compactor_new(
            base_addr: *mut c_void,
            allow_closures: u8,
        ) -> *mut c_void /* object_compactor* */;
        fn lean_compact_compactor_free(c: *mut c_void);
        fn lean_compact_compactor_insert(c: *mut c_void, o: *mut LeanObject);
        fn lean_compact_compactor_size(c: *const c_void) -> usize;
        fn lean_compact_compactor_data(c: *const c_void) -> *const c_void;
        fn lean_compact_compactor_base_addr(c: *const c_void) -> *const c_void;

        // compacted_region lifecycle
        fn lean_compact_region_new(
            sz: usize,
            data: *mut c_void,
            base_addr: *mut c_void,
            is_mmap: u8,
        ) -> *mut c_void /* compacted_region* */;
        fn lean_compact_region_free(r: *mut c_void);
        fn lean_compact_region_read(r: *mut c_void) -> *mut LeanObject;
        fn lean_compact_region_is_mmap(r: *const c_void) -> u8;
        fn lean_compact_region_size(r: *const c_void) -> usize;

        // get_loaded_libs (returns malloc-allocated array, caller frees)
        fn lean_compact_get_loaded_libs_count() -> usize;

        // malloc / free passthrough (for the compactor buffer)
        fn lean_compact_malloc(sz: usize) -> *mut c_void;
        fn lean_compact_free(p: *mut c_void);
        fn lean_compact_memcpy(dst: *mut c_void, src: *const c_void, n: usize);
    }

    // ---------------------------------------------------------------------------
    // lean_compacted_region_is_memory_mapped
    // extern "C" LEAN_EXPORT uint8 lean_compacted_region_is_memory_mapped(usize region)
    // ---------------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_is_memory_mapped(region: usize) -> u8 {
        lean_compact_region_is_mmap(region as *const c_void)
    }

    // ---------------------------------------------------------------------------
    // lean_compacted_region_size
    // extern "C" LEAN_EXPORT usize lean_compacted_region_size(usize region)
    // ---------------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_size(region: usize) -> usize {
        lean_compact_region_size(region as *const c_void)
    }

    // ---------------------------------------------------------------------------
    // lean_compacted_region_free
    // extern "C" LEAN_EXPORT obj_res lean_compacted_region_free(usize region, object *)
    // ---------------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_free(
        region: usize,
        _world: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_compact_region_free(region as *mut c_void);
        lean_io_result_mk_ok(lean_box(0))
    }
}
