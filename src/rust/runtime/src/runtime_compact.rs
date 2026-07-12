/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of src/runtime/compact.cpp (compacted_region reader side).
The lean_cxx_compacted_region_{is_memory_mapped,size,free} shims have been
removed from compact.cpp; these Rust functions are now the primary
implementations.
*/

/// Rust replacement for C++ `compacted_region` class.
///
/// The layout is `#[repr(C)]` and matches the C++ `compacted_region` class
/// for every field that C++ accesses when a `OleanCompactedRegion *` is cast
/// to `compacted_region *` by `lean_cxx_compacted_region_save` in module.cpp:
///
///   C++ offset  0 : `size_t   m_size`
///   C++ offset  8 : `void *   m_base_addr`
///   C++ offset 16 : `bool     m_is_mmap`
///   C++ offset 17 : 7-byte padding (to align `std::function<void()>`)
///   C++ offset 24 : `std::function<void()> m_free_data`  (32 bytes on Linux/x86-64)
///   C++ offset 56 : `void *   m_begin`
///   C++ offset 64 : `void *   m_next`   (unused from Rust)
///   C++ offset 72 : `void *   m_end`    (unused from Rust)
///   C++ offset 80+: std::vector fields  (not accessed on dep-region pointers)
///
/// Fields after offset 80 are Rust-only and are not accessed by C++ code.
#[repr(C)]
pub struct OleanCompactedRegion {
    /// usize of the compacted data section (matches C++ `m_size` at offset 0).
    pub m_size: usize,
    /// Saved base address from the olean header (matches C++ `m_base_addr` at offset 8).
    pub m_base_addr: usize,
    /// true if data was mmap'd, false if malloc'd (matches C++ `m_is_mmap` at offset 16).
    pub m_is_mmap: bool,
    /// 7-byte padding + 32-byte std::function placeholder to match C++ layout.
    /// C++ accesses `m_begin` at offset 56 via the `begin()` accessor.
    _free_data_placeholder: [u8; 39],
    /// Actual in-memory address of the data section start (matches C++ `m_begin` at offset 56).
    pub m_begin: usize,
    /// Placeholder for C++ `m_next` at offset 64 (not used from Rust).
    _m_next: usize,
    /// Placeholder for C++ `m_end` at offset 72 (not used from Rust).
    _m_end: usize,
    // --- Rust-only fields below (C++ does not access these for dep-region queries) ---
    /// Base of the file-level allocation (the `buffer` pointer from the read function).
    pub m_ptr: *mut u8,
    /// Total size of the allocation (= file size; used for munmap).
    pub m_alloc_size: usize,
}

// Verify that key field offsets match the C++ compacted_region layout.
const OLEAN_COMPACTED_REGION_LAYOUT_ASSERT: () = {
    assert!(core::mem::offset_of!(OleanCompactedRegion, m_size) == 0);
    assert!(core::mem::offset_of!(OleanCompactedRegion, m_base_addr) == 8);
    assert!(core::mem::offset_of!(OleanCompactedRegion, m_is_mmap) == 16);
    assert!(core::mem::offset_of!(OleanCompactedRegion, m_begin) == 56);
};

unsafe impl Send for OleanCompactedRegion {}
unsafe impl Sync for OleanCompactedRegion {}

mod runtime_compact_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

    // lean_compacted_region_is_memory_mapped(region : USize) : Bool
    #[no_mangle]
    pub unsafe fn lean_compacted_region_is_memory_mapped(region: usize) -> bool {
        if region == 0 {
            return false;
        }
        let r = &*(region as *const OleanCompactedRegion);
        r.m_is_mmap
    }

    // lean_compacted_region_size(region : USize) : USize
    #[no_mangle]
    pub unsafe fn lean_compacted_region_size(region: usize) -> usize {
        if region == 0 {
            return 0;
        }
        let r = &*(region as *const OleanCompactedRegion);
        r.m_size
    }

    // lean_compacted_region_free(region : USize) : IO Unit
    #[no_mangle]
    pub unsafe fn lean_compacted_region_free(
        region: usize,
        _io: *mut LeanObject,
    ) -> *mut LeanObject {
        if region != 0 {
            let r = Box::from_raw(region as *mut OleanCompactedRegion);
            if r.m_is_mmap {
                libc::munmap(r.m_ptr as *mut libc::c_void, r.m_alloc_size);
            } else if !r.m_ptr.is_null() {
                libc::free(r.m_ptr as *mut libc::c_void);
            }
            // `r` is dropped; OleanCompactedRegion has no Drop impl (handled above)
            core::mem::forget(r);
        }
        lean_io_result_mk_ok(lean_box(0))
    }
}
