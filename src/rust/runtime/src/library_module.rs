/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of src/library/module.cpp:
  lean_compacted_region_read — fully implemented in Rust
  lean_compacted_region_save — implemented in runtime_compact_writer.rs
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_module_impl {
    use super::*;
    use core::ffi::{c_char, c_int, c_void, CStr};

    // olean file header layout (88 bytes, verified by static_assert in module.cpp):
    //   marker[5]        {'o','l','e','a','n'}
    //   version: u8      2 = no closures, 3 = closures
    //   flags: u8        bit 0 = GMP
    //   lean_version[33]
    //   githash[40]
    //   base_addr: usize (address for the whole file including header)
    const OLEAN_HEADER_SIZE: usize = 88;
    const OLEAN_MARKER: &[u8; 5] = b"olean";
    const OLEAN_VERSION_V2: u8 = 2;
    const OLEAN_VERSION_V3: u8 = 3;
    #[cfg(lean_use_gmp)]
    const OLEAN_FLAGS_GMP: u8 = 0b1;
    #[cfg(not(lean_use_gmp))]
    const OLEAN_FLAGS_GMP: u8 = 0b0;

    // v3 format extra header: 8 bytes data_size right after the 88-byte header.
    const OLEAN_V3_DATA_SIZE_FIELD: usize = core::mem::size_of::<usize>();

    // Object tag constants matching lean.h
    const LEAN_MAX_CTOR_TAG: u8 = 243;
    const LEAN_CLOSURE_TAG: u8 = 245;
    const LEAN_ARRAY_TAG: u8 = 246;
    const LEAN_SCALAR_ARRAY_TAG: u8 = 248;
    const LEAN_STRING_TAG: u8 = 249;
    const LEAN_MPZ_TAG: u8 = 250;
    const LEAN_THUNK_TAG: u8 = 251;
    const LEAN_TASK_TAG: u8 = 252;
    const LEAN_REF_TAG: u8 = 253;
    const LEAN_PROMISE_TAG: u8 = 244;

    // Size of fixed Lean object types (LP64):
    //   lean_thunk_object  = { header(8), value(8), closure(8) } = 24
    //   lean_ref_object    = { header(8), value(8) }             = 16
    //   lean_task_object   = { header(8), value(8), imp(8) }     = 24
    //   lean_promise_object = { header(8), result(8) }           = 16
    //   mpz_object (GMP)   = { header(8), __mpz_struct(16) }     = 24
    const LEAN_THUNK_OBJECT_SIZE: usize = 24;
    const LEAN_REF_OBJECT_SIZE: usize = 16;
    const LEAN_TASK_OBJECT_SIZE: usize = 24;
    const LEAN_PROMISE_OBJECT_SIZE: usize = 16;
    #[cfg(lean_use_gmp)]
    const LEAN_MPZ_OBJECT_HEADER_SIZE: usize = 24; // header(8) + __mpz_struct(16)
    #[cfg(lean_use_gmp)]
    const LEAN_MP_LIMB_SIZE: usize = 8; // sizeof(mp_limb_t) on LP64

    // Byte offset of _mp_d within mpz_object (GMP):
    //   header(8) + _mp_alloc(4) + _mp_size(4) = 16
    #[cfg(lean_use_gmp)]
    const LEAN_MPZ_MP_D_OFFSET: usize = 16;
    #[cfg(lean_use_gmp)]
    const LEAN_MPZ_MP_SIZE_OFFSET: usize = 12; // offset of _mp_size (i32)

    // On Linux 4.17+ MAP_FIXED_NOREPLACE atomically rejects mappings at taken addresses.
    // Older kernels silently ignore the flag. We define it unconditionally if not already defined.
    #[cfg(target_os = "linux")]
    const MAP_FIXED_NOREPLACE: libc::c_int = 0x100000;

    // Pointer alignment constant (size of void* = 8 on LP64).
    const PTR_SIZE: usize = core::mem::size_of::<usize>();

    /// Round `d` up to the next multiple of PTR_SIZE.
    #[inline]
    fn align_up_ptr(d: usize) -> usize {
        let rem = d % PTR_SIZE;
        if rem != 0 {
            d + PTR_SIZE - rem
        } else {
            d
        }
    }

    /// Info about a dependency region needed for cross-region pointer fixup.
    struct DepRegionInfo {
        m_begin: usize,
        m_base_addr: usize,
        m_size: usize,
    }

    /// Info about a loaded library (used for closure fn-ptr relocation).
    struct LibInfo {
        base_addr: usize,
        id: std::string::String,
    }

    /// Extract dep-region info from the Lean `Array CompactedRegion` argument.
    /// Each array element is `lean_box_usize(region_ptr)`.
    unsafe fn extract_dep_regions(arr: *mut LeanObject) -> Vec<DepRegionInfo> {
        let n = lean_array_size(arr);
        let mut result = Vec::with_capacity(n);
        for i in 0..n {
            let elem = lean_array_get(arr, i);
            let ptr = lean_unbox_usize_val(elem);
            if ptr == 0 {
                continue;
            }
            let region = &*(ptr as *const OleanCompactedRegion);
            result.push(DepRegionInfo {
                m_begin: region.m_begin,
                m_base_addr: region.m_base_addr,
                m_size: region.m_size,
            });
        }
        // Sort by m_base_addr for binary search in fix_object_ptr.
        result.sort_by_key(|d| d.m_base_addr);
        result
    }

    /// Box a `usize` value as a Lean `USize` (= `CompactedRegion`) object.
    /// Matches C++ `box_size_t(v)` = `alloc_cnstr(0, 0, sizeof(usize))` + set scalar.
    unsafe fn lean_box_usize_val(v: usize) -> *mut LeanObject {
        let r = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<usize>() as core::ffi::c_uint);
        lean_ctor_set_uint64(r, 0, v as u64);
        r
    }

    /// Unbox a Lean `USize` to get the raw `usize`.
    /// Matches C++ `lean_unbox_usize(o)` = `cnstr_get_usize(o, 0)`.
    unsafe fn lean_unbox_usize_val(o: *mut LeanObject) -> usize {
        lean_ctor_get_uint64(o, 0) as usize
    }

    /// Create an IO error result from a Rust string.
    unsafe fn io_error_str(msg: std::string::String) -> *mut LeanObject {
        let cstr = std::ffi::CString::new(msg)
            .unwrap_or_else(|_| std::ffi::CString::new("(error message contains NUL)").unwrap());
        let msg_obj = lean_mk_string(cstr.as_ptr());
        let err = lean_mk_io_user_error(msg_obj);
        lean_io_result_mk_error(err)
    }

    /// Read exactly `n` bytes from `fd` into `buf`, handling EINTR.
    /// Returns `n` on success, a negative value on error, or `< n` on EOF.
    unsafe fn readn(fd: c_int, buf: *mut u8, n: usize) -> isize {
        let mut total: usize = 0;
        while total < n {
            let r = libc::read(fd, buf.add(total).cast::<c_void>(), n - total);
            if r < 0 {
                if *libc::__errno_location() == libc::EINTR {
                    continue;
                }
                return -1;
            }
            if r == 0 {
                break;
            }
            total += r as usize;
        }
        total as isize
    }

    // -------------------------------------------------------------------------
    // Library relocation for closure fn-pointer fixup (v3 format)
    // -------------------------------------------------------------------------

    /// Get currently loaded shared libraries with their load base addresses.
    #[cfg(target_os = "linux")]
    unsafe fn get_loaded_libs() -> Vec<LibInfo> {
        struct State {
            libs: Vec<LibInfo>,
        }
        unsafe extern "C" fn callback(
            info: *mut libc::dl_phdr_info,
            _size: libc::size_t,
            data: *mut c_void,
        ) -> c_int {
            let state = &mut *(data as *mut State);
            let id = if !(*info).dlpi_name.is_null() {
                CStr::from_ptr((*info).dlpi_name)
                    .to_string_lossy()
                    .into_owned()
            } else {
                std::string::String::new()
            };
            state.libs.push(LibInfo {
                base_addr: (*info).dlpi_addr as usize,
                id,
            });
            0
        }
        let mut state = State { libs: Vec::new() };
        libc::dl_iterate_phdr(Some(callback), &mut state as *mut State as *mut c_void);
        state.libs.sort_by_key(|l| l.base_addr);
        state.libs
    }

    #[cfg(target_os = "macos")]
    unsafe fn get_loaded_libs() -> Vec<LibInfo> {
        extern "C" {
            fn _dyld_image_count() -> u32;
            fn _dyld_get_image_header(image_index: u32) -> *const u8;
            fn _dyld_get_image_name(image_index: u32) -> *const c_char;
        }
        let n = _dyld_image_count();
        let mut libs = Vec::with_capacity(n as usize);
        for i in 0..n {
            let hdr = _dyld_get_image_header(i);
            if hdr.is_null() {
                continue;
            }
            let name_ptr = _dyld_get_image_name(i);
            if name_ptr.is_null() {
                continue;
            }
            let id = CStr::from_ptr(name_ptr).to_string_lossy().into_owned();
            libs.push(LibInfo {
                base_addr: hdr as usize,
                id,
            });
        }
        libs.sort_by_key(|l| l.base_addr);
        libs
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    unsafe fn get_loaded_libs() -> Vec<LibInfo> {
        Vec::new()
    }

    /// Parse the on-disk lib relocation table starting at `p`.
    /// Returns sorted `(old_base, delta)` pairs.
    unsafe fn read_lib_relocs(
        mut p: *const u8,
    ) -> Result<Vec<(usize, isize)>, std::string::String> {
        let mut n: u32 = 0;
        core::ptr::copy_nonoverlapping(p, &mut n as *mut u32 as *mut u8, 4);
        p = p.add(4);
        if n == 0 {
            return Ok(Vec::new());
        }
        let current_libs = get_loaded_libs();
        let mut relocs = Vec::with_capacity(n as usize);
        for _ in 0..n {
            let mut old_base: usize = 0;
            core::ptr::copy_nonoverlapping(
                p,
                &mut old_base as *mut usize as *mut u8,
                core::mem::size_of::<usize>(),
            );
            p = p.add(core::mem::size_of::<usize>());
            let mut len: u32 = 0;
            core::ptr::copy_nonoverlapping(p, &mut len as *mut u32 as *mut u8, 4);
            p = p.add(4);
            let id = CStr::from_ptr(p.cast::<c_char>())
                .to_bytes()
                .get(..len as usize)
                .map(|b| std::str::from_utf8(b).unwrap_or("").to_owned())
                .unwrap_or_default();
            p = p.add(len as usize);
            let mut new_base: usize = 0;
            let mut found = false;
            for lib in &current_libs {
                if lib.id == id {
                    new_base = lib.base_addr;
                    found = true;
                    break;
                }
            }
            if !found {
                return Err(format!(
                    "library required for closure relocation is not loaded in this process: '{id}'"
                ));
            }
            let delta = new_base as isize - old_base as isize;
            relocs.push((old_base, delta));
        }
        relocs.sort_by_key(|r| r.0);
        Ok(relocs)
    }

    // -------------------------------------------------------------------------
    // Pointer fixup
    // -------------------------------------------------------------------------

    /// Translate a compacted pointer from saved (base_addr-relative) to actual address.
    /// Scalar pointers are returned unchanged.
    #[inline]
    unsafe fn fix_object_ptr(
        o: *mut LeanObject,
        m_begin: usize,
        m_base_addr: usize,
        m_size: usize,
        dep_regions: &[DepRegionInfo],
    ) -> *mut LeanObject {
        if lean_is_scalar(o) {
            return o;
        }
        let addr = o as usize;
        // Own region (most common case).
        if addr >= m_base_addr && addr < m_base_addr + m_size {
            return (m_begin + (addr - m_base_addr)) as *mut LeanObject;
        }
        // Binary search dep regions sorted by m_base_addr.
        let idx = dep_regions.partition_point(|d| d.m_base_addr <= addr);
        if idx > 0 {
            let dep = &dep_regions[idx - 1];
            if addr < dep.m_base_addr + dep.m_size {
                return (dep.m_begin + (addr - dep.m_base_addr)) as *mut LeanObject;
            }
        }
        // No region matched: should not happen with valid olean data.
        o
    }

    // -------------------------------------------------------------------------
    // Fixup walk (corresponds to compacted_region::read() in compact.cpp)
    // -------------------------------------------------------------------------

    /// Perform the compacted-region fixup walk. Returns the root object.
    /// `m_begin` and `m_base_addr` are for the DATA section (not the whole file).
    unsafe fn compact_region_read(
        m_begin: usize,
        m_base_addr: usize,
        m_size: usize,
        dep_regions: &[DepRegionInfo],
        lib_relocs: &[(usize, isize)],
        closure_offsets: &[usize],
    ) -> *mut LeanObject {
        let data_ptr = m_begin as *mut u8;
        let m_end = m_begin + m_size;

        // First `sizeof(usize)` bytes = root object's saved (base_addr-relative) pointer.
        let root_raw = (data_ptr as *const usize).read() as *mut LeanObject;
        let root = fix_object_ptr(root_raw, m_begin, m_base_addr, m_size, dep_regions);

        // Apply closure fn-pointer relocations if needed.
        let needs_fn_reloc = lib_relocs.iter().any(|&(_, delta)| delta != 0);
        if needs_fn_reloc && !closure_offsets.is_empty() {
            for &off in closure_offsets {
                let fn_field = data_ptr.add(off).cast::<usize>();
                let fn_ptr = fn_field.read();
                // Binary search for the library whose range contains fn_ptr.
                let idx = lib_relocs.partition_point(|&(base, _)| base <= fn_ptr);
                if idx > 0 {
                    let delta = lib_relocs[idx - 1].1;
                    if delta != 0 {
                        fn_field.write((fn_ptr as isize + delta) as usize);
                    }
                }
            }
        }

        // If own region landed at saved base_addr, own-region pointers are already
        // correct.  Only need the walk if a dep region missed its base_addr.
        if m_begin == m_base_addr {
            let needs_dep_reloc = dep_regions.iter().any(|d| d.m_begin != d.m_base_addr);
            if !needs_dep_reloc {
                return root;
            }
        }

        // Full object walk: patch pointers in every compacted object.
        let mut m_next = data_ptr.add(core::mem::size_of::<usize>()); // skip root offset
        while (m_next as usize) < m_end {
            let curr = m_next as *mut LeanObject;
            let tag = (*curr).tag;
            let advance = if tag <= LEAN_MAX_CTOR_TAG {
                // Constructor: fix each object-pointer field.
                let num_objs = (*curr).other as usize;
                let field_ptr = curr.add(1) as *mut *mut LeanObject;
                for i in 0..num_objs {
                    let fp = field_ptr.add(i);
                    *fp = fix_object_ptr(*fp, m_begin, m_base_addr, m_size, dep_regions);
                }
                runtime_object_size_impl::lean_object_byte_size(curr)
            } else {
                match tag {
                    LEAN_CLOSURE_TAG => {
                        // Fix captured object pointers only; m_fun was relocated above.
                        let c = curr as *const LeanClosureObject;
                        let num_fixed = (*c).num_fixed as usize;
                        let data_ptr2 = c.add(1) as *mut *mut LeanObject;
                        for i in 0..num_fixed {
                            let fp = data_ptr2.add(i);
                            *fp = fix_object_ptr(*fp, m_begin, m_base_addr, m_size, dep_regions);
                        }
                        runtime_object_size_impl::lean_object_byte_size(curr)
                    }
                    LEAN_ARRAY_TAG => {
                        let arr = curr as *const LeanArrayObject;
                        let n = (*arr).size;
                        let elems = arr.add(1) as *mut *mut LeanObject;
                        for i in 0..n {
                            let fp = elems.add(i);
                            *fp = fix_object_ptr(*fp, m_begin, m_base_addr, m_size, dep_regions);
                        }
                        runtime_object_size_impl::lean_object_byte_size(curr)
                    }
                    LEAN_SCALAR_ARRAY_TAG => {
                        // No pointer fields; advance by byte size.
                        runtime_object_size_impl::lean_object_byte_size(curr)
                    }
                    LEAN_STRING_TAG => {
                        // No pointer fields.
                        runtime_object_size_impl::lean_object_byte_size(curr)
                    }
                    LEAN_MPZ_TAG => {
                        #[cfg(lean_use_gmp)]
                        {
                            // Fix _mp_d: stored as m_base_addr-relative, convert to m_begin-relative.
                            let mp_d_field =
                                (curr as *mut u8).add(LEAN_MPZ_MP_D_OFFSET).cast::<usize>();
                            let old_mp_d = mp_d_field.read();
                            mp_d_field.write(m_begin + (old_mp_d - m_base_addr));
                        }
                        // cs_size was set by lean_set_non_heap_header to include limb data.
                        runtime_object_size_impl::lean_object_byte_size(curr)
                    }
                    LEAN_THUNK_TAG => {
                        // Fix m_value at offset 8.
                        let vp = (curr as *mut u8).add(8).cast::<*mut LeanObject>();
                        *vp = fix_object_ptr(*vp, m_begin, m_base_addr, m_size, dep_regions);
                        LEAN_THUNK_OBJECT_SIZE
                    }
                    LEAN_REF_TAG => {
                        // Fix m_value at offset 8.
                        let vp = (curr as *mut u8).add(8).cast::<*mut LeanObject>();
                        *vp = fix_object_ptr(*vp, m_begin, m_base_addr, m_size, dep_regions);
                        LEAN_REF_OBJECT_SIZE
                    }
                    LEAN_TASK_TAG => {
                        // Fix m_value (AtomicPtr<LeanObject>) at offset 8.
                        let vp = (curr as *mut u8).add(8).cast::<*mut LeanObject>();
                        *vp = fix_object_ptr(*vp, m_begin, m_base_addr, m_size, dep_regions);
                        LEAN_TASK_OBJECT_SIZE
                    }
                    LEAN_PROMISE_TAG => {
                        // Fix m_result at offset 8.
                        let vp = (curr as *mut u8).add(8).cast::<*mut LeanObject>();
                        *vp = fix_object_ptr(*vp, m_begin, m_base_addr, m_size, dep_regions);
                        LEAN_PROMISE_OBJECT_SIZE
                    }
                    _ => {
                        // Unknown tag: use lean_object_byte_size as best effort.
                        runtime_object_size_impl::lean_object_byte_size(curr)
                    }
                }
            };
            m_next = m_next.add(align_up_ptr(advance));
        }

        root
    }

    // -------------------------------------------------------------------------
    // Public FFI entry points
    // -------------------------------------------------------------------------

    /// Load a compacted olean region from `ofname`.
    ///
    /// Port of C++ `lean_cxx_compacted_region_read` from src/library/module.cpp.
    /// Returns `IO (α × CompactedRegion)` where the second element is a boxed `USize`
    /// holding the raw `*OleanCompactedRegion` pointer.
    #[no_mangle]
    pub unsafe extern "C" fn lean_compacted_region_read(
        ofname: *mut LeanObject,
        odep_regions: *mut LeanObject,
        _io: *mut LeanObject,
    ) -> *mut LeanObject {
        let fname_ptr = lean_string_cstr(ofname);
        let olean_fn = CStr::from_ptr(fname_ptr).to_string_lossy();

        // Open the file.
        #[cfg(not(target_os = "windows"))]
        let fd = {
            let fd = libc::open(fname_ptr, libc::O_RDONLY);
            if fd < 0 {
                return io_error_str(format!(
                    "failed to open file '{}': {}",
                    olean_fn,
                    CStr::from_ptr(libc::strerror(*libc::__errno_location())).to_string_lossy()
                ));
            }
            fd
        };

        struct FdGuard(c_int);
        impl Drop for FdGuard {
            fn drop(&mut self) {
                if self.0 >= 0 {
                    unsafe {
                        libc::close(self.0);
                    }
                }
            }
        }
        let _fd_guard = FdGuard(fd);

        // Stat the file to get its size.
        let mut st: libc::stat = core::mem::zeroed();
        if libc::fstat(fd, &mut st) < 0 {
            return io_error_str(format!(
                "failed to stat file '{}': {}",
                olean_fn,
                CStr::from_ptr(libc::strerror(*libc::__errno_location())).to_string_lossy()
            ));
        }
        let file_size = st.st_size as usize;

        // Read the 88-byte header.
        let mut header_buf = [0u8; OLEAN_HEADER_SIZE];
        let n_read = readn(fd, header_buf.as_mut_ptr(), OLEAN_HEADER_SIZE);
        if n_read < 0 {
            return io_error_str(format!(
                "failed to read file '{}': {}",
                olean_fn,
                CStr::from_ptr(libc::strerror(*libc::__errno_location())).to_string_lossy()
            ));
        }
        if n_read as usize != OLEAN_HEADER_SIZE {
            return io_error_str(format!(
                "failed to read file '{}', invalid header",
                olean_fn
            ));
        }
        if &header_buf[..5] != OLEAN_MARKER {
            return io_error_str(format!(
                "failed to read file '{}', invalid header",
                olean_fn
            ));
        }
        let version = header_buf[5];
        let flags = header_buf[6];
        if (version != OLEAN_VERSION_V2 && version != OLEAN_VERSION_V3) || flags != OLEAN_FLAGS_GMP
        {
            return io_error_str(format!(
                "failed to read file '{}', incompatible header",
                olean_fn
            ));
        }
        // base_addr is stored at offset 80 (5+1+1+33+40 = 80).
        let mut base_addr: usize = 0;
        core::ptr::copy_nonoverlapping(
            header_buf.as_ptr().add(80),
            &mut base_addr as *mut usize as *mut u8,
            core::mem::size_of::<usize>(),
        );

        // Extract dep regions from the Lean array.
        let dep_regions = extract_dep_regions(odep_regions);

        // Map or allocate the file into memory.
        let mut buffer: *mut u8 = core::ptr::null_mut();
        let mut is_mmap = false;

        #[cfg(not(target_os = "windows"))]
        {
            // Try mmap at base_addr (MAP_PRIVATE | MAP_FIXED_NOREPLACE on Linux).
            let mmap_flags = {
                let mut f = libc::MAP_PRIVATE;
                #[cfg(target_os = "linux")]
                {
                    f |= MAP_FIXED_NOREPLACE;
                }
                f
            };
            let ptr = libc::mmap(
                base_addr as *mut c_void,
                file_size,
                libc::PROT_READ | libc::PROT_WRITE,
                mmap_flags,
                fd,
                0,
            );
            if ptr != libc::MAP_FAILED && ptr == base_addr as *mut c_void {
                buffer = ptr as *mut u8;
                is_mmap = true;
            } else {
                if ptr != libc::MAP_FAILED {
                    libc::munmap(ptr, file_size);
                }
            }
        }

        if buffer.is_null() {
            // Fallback: malloc + read.
            buffer = libc::malloc(file_size) as *mut u8;
            if buffer.is_null() {
                return io_error_str(format!("out of memory reading '{}'", olean_fn));
            }
            libc::lseek(fd, 0, libc::SEEK_SET);
            let r = readn(fd, buffer, file_size);
            if r < 0 || r as usize != file_size {
                libc::free(buffer as *mut c_void);
                return io_error_str(format!("failed to read file '{}'", olean_fn));
            }
        }

        // Parse v3 sections if needed; default to v2 (no closures).
        let mut lib_relocs: Vec<(usize, isize)> = Vec::new();
        let mut closure_offsets: Vec<usize> = Vec::new();
        let data_section_off;
        let data_section_sz;

        if version == OLEAN_VERSION_V3 {
            // v3: [header(88)][data_size(8)][data][num_closure_offsets(4)][closure_off(8*n)][lib_table]
            data_section_off = OLEAN_HEADER_SIZE + OLEAN_V3_DATA_SIZE_FIELD;
            let mut data_size: usize = 0;
            core::ptr::copy_nonoverlapping(
                buffer.add(OLEAN_HEADER_SIZE),
                &mut data_size as *mut usize as *mut u8,
                core::mem::size_of::<usize>(),
            );
            data_section_sz = data_size;

            // Closure offsets section starts after data.
            let mut p = buffer.add(data_section_off + data_size);
            let mut num_co: u32 = 0;
            core::ptr::copy_nonoverlapping(p, &mut num_co as *mut u32 as *mut u8, 4);
            p = p.add(4);
            if num_co > 0 {
                closure_offsets.reserve(num_co as usize);
                for _ in 0..num_co {
                    let mut off: u64 = 0;
                    core::ptr::copy_nonoverlapping(p, &mut off as *mut u64 as *mut u8, 8);
                    p = p.add(8);
                    closure_offsets.push(off as usize);
                }
                // Parse lib relocation table.
                match read_lib_relocs(p) {
                    Ok(relocs) => lib_relocs = relocs,
                    Err(msg) => {
                        if is_mmap {
                            libc::munmap(buffer as *mut c_void, file_size);
                        } else {
                            libc::free(buffer as *mut c_void);
                        }
                        return io_error_str(format!("failed to read '{}': {msg}", olean_fn));
                    }
                }
            }
        } else {
            // v2: [header(88)][data]
            data_section_off = OLEAN_HEADER_SIZE;
            data_section_sz = file_size - OLEAN_HEADER_SIZE;
        }

        let m_begin = buffer as usize + data_section_off;
        let m_base_addr = base_addr + data_section_off;

        // Perform the fixup walk (equivalent to compacted_region::read()).
        let mod_obj = compact_region_read(
            m_begin,
            m_base_addr,
            data_section_sz,
            &dep_regions,
            &lib_relocs,
            &closure_offsets,
        );

        // Create the OleanCompactedRegion that owns the allocation.
        // Field order must match #[repr(C)] layout (see runtime_compact.rs).
        let region = Box::new(OleanCompactedRegion {
            m_size: data_section_sz,
            m_base_addr: m_base_addr,
            m_is_mmap: is_mmap,
            _free_data_placeholder: [0u8; 39],
            m_begin: m_begin,
            _m_next: 0,
            _m_end: 0,
            m_ptr: buffer,
            m_alloc_size: file_size,
        });
        let region_ptr = Box::into_raw(region) as usize;

        // Return `IO.ok (Prod.mk mod (box_usize region_ptr))`.
        let pair = lean_runtime_alloc_ctor(0, 2, 0);
        lean_runtime_ctor_set(pair, 0, mod_obj);
        lean_runtime_ctor_set(pair, 1, lean_box_usize_val(region_ptr));
        lean_io_result_mk_ok(pair)
    }
}
