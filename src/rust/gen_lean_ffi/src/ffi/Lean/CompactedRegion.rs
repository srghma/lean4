// Generated stub file for Lean FFI imports
// Source: src/Lean/CompactedRegion.lean

// lean_compacted_region_is_memory_mapped(region : USize) : Bool
#[inline]
pub unsafe fn lean_compacted_region_is_memory_mapped(region: usize) -> u8 {
    // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Lean/CompactedRegion.lean:21
    if region == 0 {
        return 0;
    }
    let r = unsafe { &*(region as *const OleanCompactedRegion) };
    r.m_is_mmap as u8
}

// lean_compacted_region_size(region : USize) : USize
#[inline]
pub unsafe fn lean_compacted_region_size(region: usize) -> usize {
    // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Lean/CompactedRegion.lean:25
    if region == 0 {
        return 0;
    }
    let r = unsafe { &*(region as *const OleanCompactedRegion) };
    r.m_size
}

// lean_compacted_region_free(region : USize) : IO Unit
// [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Lean/CompactedRegion.lean:32
#[inline]
pub(crate) unsafe fn lean_compacted_region_free(
    region: usize,
    _io: *mut LeanObject,
) -> *mut LeanObject {
    if region != 0 {
        let r = unsafe { Box::from_raw(region as *mut OleanCompactedRegion) };
        if r.m_is_mmap {
            #[cfg(not(target_os = "windows"))]
            {
                unsafe { libc::munmap(r.m_ptr as *mut libc::c_void, r.m_alloc_size) };
            }
        } else if !r.m_ptr.is_null() {
            unsafe { libc::free(r.m_ptr as *mut libc::c_void) };
        }
        // `r` is dropped; OleanCompactedRegion has no Drop impl (handled above)
        core::mem::forget(r);
    }
    unsafe { lean_io_result_mk_ok(lean_box(0)) }
}

pub fn lean_compacted_region_save<A0, A1, A2, A3, A4, A5, R>(
    _: A0,
    _: A1,
    _: A2,
    _: A3,
    _: A4,
    _: A5,
) -> R {
    todo!("Stub for lean_compacted_region_save")
}

pub fn lean_compacted_region_read<A0, A1, R>(_: A0, _: A1) -> R {
    todo!("Stub for lean_compacted_region_read")
}
