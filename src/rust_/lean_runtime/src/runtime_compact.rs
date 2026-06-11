mod runtime_compact_impl {
    use super::*;
    use core::ffi::c_void;

    #[repr(C)]
    pub(crate) struct RustCompactedRegion {
        pub size: usize,
        pub is_memory_mapped: bool,
        pub objects: Vec<*mut LeanObject>,
        pub mmap_ptr: *mut u8,
        pub mmap_size: usize,
        pub m_begin: usize,
        pub m_base_addr: usize,
    }

    impl RustCompactedRegion {
        pub(crate) fn new(size: usize, objects: Vec<*mut LeanObject>) -> Self {
            Self {
                size,
                is_memory_mapped: false,
                objects,
                mmap_ptr: core::ptr::null_mut(),
                mmap_size: 0,
                m_begin: 0,
                m_base_addr: 0,
            }
        }
    }

    // ---------------------------------------------------------------------------
    // lean_compacted_region_is_memory_mapped
    // extern "C" LEAN_EXPORT uint8 lean_compacted_region_is_memory_mapped(usize region)
    // ---------------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_is_memory_mapped(region: usize) -> u8 {
        if region == 0 {
            return 0;
        }
        let region = &*(region as *const RustCompactedRegion);
        region.is_memory_mapped as u8
    }

    // ---------------------------------------------------------------------------
    // lean_compacted_region_size
    // extern "C" LEAN_EXPORT usize lean_compacted_region_size(usize region)
    // ---------------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_size(region: usize) -> usize {
        if region == 0 {
            return 0;
        }
        let region = &*(region as *const RustCompactedRegion);
        region.size
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
        if region != 0 {
            let region = Box::from_raw(region as *mut RustCompactedRegion);
            if !region.mmap_ptr.is_null() {
                if region.is_memory_mapped {
                    #[cfg(any(target_os = "linux", target_os = "macos"))]
                    libc::munmap(region.mmap_ptr as *mut _, region.mmap_size);
                } else {
                    libc::free(region.mmap_ptr as *mut _);
                }
            } else {
                for obj in region.objects {
                    if !obj.is_null() {
                        super::lean_dealloc_export(obj as *mut u8, super::lean_object_byte_size(obj));
                    }
                }
            }
        }
        lean_io_result_mk_ok(lean_box(0))
    }
}
