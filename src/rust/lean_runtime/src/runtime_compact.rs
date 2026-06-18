/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of src/runtime/compact.cpp (compacted_region reader side).
The lean_cxx_compacted_region_{is_memory_mapped,size,free} shims have been
removed from compact.cpp; these Rust functions are now the primary
implementations.
*/

/// Rust replacement for C++ `compacted_region` class.
/// Created by `lean_compacted_region_read` and stored as a raw pointer
/// (cast to `usize`) inside a Lean `CompactedRegion` (= `USize`) value.
pub struct OleanCompactedRegion {
    /// true if data was mmap'd, false if malloc'd
    pub m_is_mmap: bool,
    /// base of the file-level allocation (the `buffer` pointer from the read function)
    pub m_ptr: *mut u8,
    /// total size of the allocation (= file size; used for munmap)
    pub m_alloc_size: usize,
    /// size of the compacted data section
    pub m_size: usize,
    /// actual in-memory address of the data section start
    pub m_begin: usize,
    /// saved base address of the data section from the olean file header
    pub m_base_addr: usize,
}

unsafe impl Send for OleanCompactedRegion {}
unsafe impl Sync for OleanCompactedRegion {}

#[cfg(feature = "export-runtime-ffi")]
mod runtime_compact_impl {
    use super::*;

    // lean_compacted_region_is_memory_mapped(region : USize) : Bool
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_is_memory_mapped(region: usize) -> u8 {
        if region == 0 {
            return 0;
        }
        let r = &*(region as *const OleanCompactedRegion);
        r.m_is_mmap as u8
    }

    // lean_compacted_region_size(region : USize) : USize
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_size(region: usize) -> usize {
        if region == 0 {
            return 0;
        }
        let r = &*(region as *const OleanCompactedRegion);
        r.m_size
    }

    // lean_compacted_region_free(region : USize) : IO Unit
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_free(
        region: usize,
        _io: *mut LeanObject,
    ) -> *mut LeanObject {
        if region != 0 {
            let r = Box::from_raw(region as *mut OleanCompactedRegion);
            if r.m_is_mmap {
                #[cfg(not(target_os = "windows"))]
                {
                    libc::munmap(r.m_ptr as *mut libc::c_void, r.m_alloc_size);
                }
            } else if !r.m_ptr.is_null() {
                libc::free(r.m_ptr as *mut libc::c_void);
            }
            // `r` is dropped; OleanCompactedRegion has no Drop impl (handled above)
            core::mem::forget(r);
        }
        lean_io_result_mk_ok(lean_box(0))
    }
}
