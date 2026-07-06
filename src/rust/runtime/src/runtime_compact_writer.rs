/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of src/runtime/compact.cpp (object_compactor) and
src/library/module.cpp (lean_cxx_compacted_region_save) to Rust.
*/

mod runtime_compact_writer_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_void};
    use core::sync::atomic::{AtomicPtr, Ordering};
    use std::collections::HashMap;
    use std::io::Write as IoWrite;

    // -------------------------------------------------------------------------
    // Constants
    // -------------------------------------------------------------------------

    const PTR_SIZE: usize = core::mem::size_of::<usize>();
    // mmap/MapViewOfFileEx addresses must be aligned to 64KB on all platforms
    const PAGE_ALIGN: usize = 1 << 16;
    const COMPACTOR_INIT_SZ: usize = 1024 * 1024;

    const OLEAN_HEADER_SIZE: usize = 88;
    const OLEAN_MARKER: &[u8; 5] = b"olean";
    const OLEAN_VERSION_V2: u8 = 2;
    const OLEAN_VERSION_V3: u8 = 3;
    #[cfg(lean_use_gmp)]
    const OLEAN_FLAGS_GMP: u8 = 0b1;
    #[cfg(not(lean_use_gmp))]
    const OLEAN_FLAGS_GMP: u8 = 0b0;

    const LEAN_GITHASH: &str = env!("LEAN_RUST_GITHASH");

    // Object tag constants matching lean.h
    const LEAN_MAX_CTOR_TAG: u8 = 243; // duplicate in undefined at line 38 (🔁)
    const LEAN_PROMISE_TAG: u8 = 244; // duplicate in undefined at line 39 (🔁)
    const LEAN_CLOSURE_TAG: u8 = 245; // duplicate in undefined at line 40 (🔁)
    const LEAN_ARRAY_TAG: u8 = 246; // duplicate in undefined at line 41 (🔁)
    const LEAN_SCALAR_ARRAY_TAG: u8 = 248; // duplicate in undefined at line 42 (🔁)
    const LEAN_STRING_TAG: u8 = 249; // duplicate in undefined at line 43 (🔁)
    const LEAN_MPZ_TAG: u8 = 250; // duplicate in undefined at line 44 (🔁)
    const LEAN_THUNK_TAG: u8 = 251; // duplicate in undefined at line 45 (🔁)
    const LEAN_TASK_TAG: u8 = 252; // duplicate in undefined at line 46 (🔁)
    const LEAN_REF_TAG: u8 = 253; // duplicate in undefined at line 47 (🔁)
    const LEAN_EXTERNAL_TAG: u8 = 254; // duplicate in undefined at line 48 (🔁)

    // lean_closure_object layout (matching lean.h uint16_t fields):
    //   header(8) + fun(8) + arity(u16,2) + num_fixed(u16,2) + pad(4) = 24 bytes header
    //   args start at offset 24
    const LEAN_CLOSURE_FUN_OFFSET: usize = 8;
    const LEAN_CLOSURE_NUM_FIXED_OFFSET: usize = 18;
    const LEAN_CLOSURE_ARGS_OFFSET: usize = 24;

    // Offset of the single pointer/value field in thunk/ref/task/promise objects
    const LEAN_VALUE_OFFSET: usize = 8;

    // GMP mpz_object: header(8) + __mpz_struct(16 = alloc(4)+size(4)+d_ptr(8)) = 24 bytes
    #[cfg(lean_use_gmp)]
    const LEAN_MPZ_OBJECT_SIZE: usize = 24;
    #[cfg(lean_use_gmp)]
    const LEAN_MPZ_MP_ALLOC_OFFSET: usize = 8;
    #[cfg(lean_use_gmp)]
    const LEAN_MPZ_MP_SIZE_OFFSET: usize = 12;
    #[cfg(lean_use_gmp)]
    const LEAN_MPZ_MP_D_OFFSET: usize = 16;
    #[cfg(lean_use_gmp)]
    const LEAN_MP_LIMB_SIZE: usize = 8; // sizeof(mp_limb_t) on LP64

    // Non-GMP mpz_object: header(8) + mpz_value(24) = 32 bytes
    // mpz_value: sign(bool@0,1) + pad(7) + size(usize@8) + digits(*mpn@16) = 24 bytes
    #[cfg(not(lean_use_gmp))]
    const LEAN_MPZ_OBJECT_SIZE: usize = 32;
    #[cfg(not(lean_use_gmp))]
    const LEAN_MPZ_SIGN_OFFSET: usize = 8;
    #[cfg(not(lean_use_gmp))]
    const LEAN_MPZ_SIZE_OFFSET: usize = 16;
    #[cfg(not(lean_use_gmp))]
    const LEAN_MPZ_DIGITS_OFFSET: usize = 24;
    #[cfg(not(lean_use_gmp))]
    const LEAN_MPN_DIGIT_SIZE: usize = 4; // sizeof(unsigned int)

    // -------------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------------

    #[inline]
    fn align_up_ptr(sz: usize) -> usize {
        let rem = sz % PTR_SIZE;
        if rem != 0 { sz + PTR_SIZE - rem } else { sz }
    }

    /// Read the cached hash stored in a Lean Name object.
    /// Layout: header(8) + parent_ptr(8) + component_ptr(8) + hash(u64,8) = 32 bytes.
    unsafe fn lean_name_hash_val(n: *mut LeanObject) -> u64 {
        if lean_is_scalar(n) {
            0 // anonymous name
        } else {
            lean_ctor_get_uint64(n, core::mem::size_of::<*mut LeanObject>() * 2)
        }
    }

    /// Get a thunk's current value (borrowed, no RC change).
    unsafe fn thunk_get_borrow(t: *mut LeanObject) -> *mut LeanObject {
        let value_atomic = (t as *mut u8).add(8).cast::<AtomicPtr<LeanObject>>();
        let v = (*value_atomic).load(Ordering::Relaxed);
        if !v.is_null() {
            v
        } else {
            runtime_object_array_impl::lean_thunk_get_core(t)
        }
    }

    // -------------------------------------------------------------------------
    // Library info (for closure fn-pointer relocation table)
    // -------------------------------------------------------------------------

    struct LibInfo {
        base_addr: usize,
        id: std::string::String,
    }

    #[cfg(target_os = "linux")]
    unsafe fn get_loaded_libs() -> Vec<LibInfo> {
        struct State {
            libs: Vec<LibInfo>,
        }
        unsafe fn callback(
            info: *mut libc::dl_phdr_info,
            _size: libc::size_t,
            data: *mut c_void,
        ) -> core::ffi::c_int {
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
        use mach2::dyld::{_dyld_get_image_header, _dyld_get_image_name, _dyld_image_count};

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
            libs.push(LibInfo {
                base_addr: hdr as usize,
                id: CStr::from_ptr(name_ptr).to_string_lossy().into_owned(),
            });
        }
        libs.sort_by_key(|l| l.base_addr);
        libs
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    unsafe fn get_loaded_libs() -> Vec<LibInfo> {
        Vec::new()
    }

    // -------------------------------------------------------------------------
    // Dep region info for the writer (sorted by actual memory address)
    // -------------------------------------------------------------------------

    struct DepRegionWriterInfo {
        m_begin: usize,     // actual memory address of data
        m_base_addr: usize, // saved base address (from olean header)
        m_size: usize,
    }

    unsafe fn extract_dep_regions_for_writer(arr: *mut LeanObject) -> Vec<DepRegionWriterInfo> {
        let n = lean_array_size(arr);
        let mut result = Vec::with_capacity(n);
        for i in 0..n {
            let elem = lean_array_get(arr, i);
            let ptr = lean_ctor_get_uint64(elem, 0) as usize;
            if ptr == 0 {
                continue;
            }
            let region = &*(ptr as *const OleanCompactedRegion);
            result.push(DepRegionWriterInfo {
                m_begin: region.m_begin,
                m_base_addr: region.m_base_addr,
                m_size: region.m_size,
            });
        }
        result.sort_by_key(|d| d.m_begin);
        result
    }

    // -------------------------------------------------------------------------
    // ObjectCompactor
    // -------------------------------------------------------------------------

    struct ObjectCompactor {
        buf: Vec<u8>,
        /// src pointer → base_addr-relative stored address
        obj_table: HashMap<usize, usize>,
        /// content bytes → base_addr-relative stored address
        max_sharing_table: HashMap<Vec<u8>, usize>,
        /// LIFO stack of pending objects (DFS traversal)
        todo: Vec<*mut LeanObject>,
        /// Temporary child-offset scratch space (reused to avoid per-call allocations)
        tmp: Vec<usize>,
        /// Dep regions sorted by m_begin (actual address) for binary search
        dep_regions: Vec<DepRegionWriterInfo>,
        /// Loaded libraries sorted by base_addr
        libs: Vec<LibInfo>,
        /// Buffer-relative offsets of m_fun fields for closures in this part
        closure_offsets: Vec<usize>,
        allow_closures: bool,
        /// Intended mmap base address for byte 0 of the buffer
        base_addr: usize,
    }

    // ObjectCompactor is not thread-safe by design (callers must ensure single-threaded use)
    unsafe impl Send for ObjectCompactor {}

    impl ObjectCompactor {
        fn new(
            base_addr: usize,
            dep_regions: Vec<DepRegionWriterInfo>,
            allow_closures: bool,
            libs: Vec<LibInfo>,
        ) -> Self {
            ObjectCompactor {
                buf: Vec::with_capacity(COMPACTOR_INIT_SZ),
                obj_table: HashMap::new(),
                max_sharing_table: HashMap::new(),
                todo: Vec::new(),
                tmp: Vec::new(),
                dep_regions,
                libs,
                closure_offsets: Vec::new(),
                allow_closures,
                base_addr,
            }
        }

        /// Allocate `sz` bytes (ptr-aligned, zeroed). Returns start offset in buf.
        fn alloc(&mut self, sz: usize) -> usize {
            let sz = align_up_ptr(sz);
            let offset = self.buf.len();
            self.buf.resize(offset + sz, 0);
            offset
        }

        /// Write the lean_object non-heap header at buf_offset.
        /// rc=0, cs_size=cs_sz, other=other, tag=tag.
        unsafe fn set_non_heap_header(
            &mut self,
            buf_offset: usize,
            cs_sz: u16,
            tag: u8,
            other: u8,
        ) {
            let p = self.buf.as_mut_ptr().add(buf_offset);
            (p as *mut i32).write(0); // rc = 0
            (p.add(4) as *mut u16).write(cs_sz); // cs_size
            *p.add(6) = other;
            *p.add(7) = tag;
        }

        /// Write non-heap header for big objects (cs_size = 1).
        unsafe fn set_non_heap_header_for_big(&mut self, buf_offset: usize, tag: u8, other: u8) {
            self.set_non_heap_header(buf_offset, 1, tag, other);
        }

        /// Copy o into buf and set its non-heap header. Returns start offset.
        unsafe fn copy_object(&mut self, o: *mut LeanObject) -> usize {
            let sz = runtime_object_size_impl::lean_object_byte_size(o);
            let offset = self.alloc(sz);
            core::ptr::copy_nonoverlapping(o as *const u8, self.buf.as_mut_ptr().add(offset), sz);
            self.set_non_heap_header(offset, sz as u16, (*o).tag, (*o).other);
            offset
        }

        /// Record src_ptr → (base_addr + buf_offset) in obj_table.
        fn save(&mut self, src_ptr: usize, buf_offset: usize) {
            self.obj_table.insert(src_ptr, self.base_addr + buf_offset);
        }

        /// Content-based dedup: if buf[buf_offset..buf_offset+sz] already in table,
        /// revert the allocation and reuse. Either way, records src_ptr in obj_table.
        fn save_max_sharing(&mut self, src_ptr: usize, buf_offset: usize, sz: usize) {
            let content = self.buf[buf_offset..buf_offset + sz].to_vec();
            if let Some(&existing) = self.max_sharing_table.get(&content) {
                self.buf.truncate(buf_offset);
                self.obj_table.insert(src_ptr, existing);
            } else {
                let stored = self.base_addr + buf_offset;
                self.max_sharing_table.insert(content, stored);
                self.obj_table.insert(src_ptr, stored);
            }
        }

        /// Convert src pointer to stored (base_addr-relative) address.
        /// Returns None and pushes o onto todo if not yet processed.
        unsafe fn to_offset(&mut self, o: *mut LeanObject) -> Option<usize> {
            if lean_is_scalar(o) {
                return Some(o as usize);
            }
            if let Some(&stored) = self.obj_table.get(&(o as usize)) {
                return Some(stored);
            }
            // Check dep regions for non-heap (compacted) objects
            if !self.dep_regions.is_empty() && (*o).rc == 0 {
                let addr = o as usize;
                let idx = self.dep_regions.partition_point(|d| d.m_begin <= addr);
                if idx > 0 {
                    let dep = &self.dep_regions[idx - 1];
                    if addr < dep.m_begin + dep.m_size {
                        let stored = dep.m_base_addr + (addr - dep.m_begin);
                        self.obj_table.insert(o as usize, stored);
                        return Some(stored);
                    }
                }
            }
            self.todo.push(o);
            None
        }

        // ----- insert_* methods -----

        unsafe fn insert_constructor(&mut self, o: *mut LeanObject) -> bool {
            let num_objs = (*o).other as usize;
            self.tmp.resize(num_objs, 0);
            let mut missing = false;
            let mut i = num_objs;
            while i > 0 {
                i -= 1;
                match self.to_offset(lean_ctor_get(o, i)) {
                    Some(off) => self.tmp[i] = off,
                    None => missing = true,
                }
            }
            if missing {
                return false;
            }
            let new_off = self.copy_object(o);
            for i in 0..num_objs {
                (self.buf.as_mut_ptr().add(new_off + 8 + i * PTR_SIZE) as *mut usize)
                    .write(self.tmp[i]);
            }
            let sz = runtime_object_size_impl::lean_object_byte_size(o);
            self.save_max_sharing(o as usize, new_off, sz);
            true
        }

        unsafe fn insert_array(&mut self, o: *mut LeanObject) -> bool {
            let n = lean_array_size(o);
            self.tmp.resize(n, 0);
            let mut missing = false;
            let mut i = n;
            while i > 0 {
                i -= 1;
                match self.to_offset(lean_array_get(o, i)) {
                    Some(off) => self.tmp[i] = off,
                    None => missing = true,
                }
            }
            if missing {
                return false;
            }
            let obj_sz = core::mem::size_of::<LeanArrayObject>() + PTR_SIZE * n;
            let new_off = self.alloc(obj_sz);
            self.set_non_heap_header_for_big(new_off, LEAN_ARRAY_TAG, 0);
            let p = self.buf.as_mut_ptr().add(new_off);
            (p.add(8) as *mut usize).write(n);
            (p.add(16) as *mut usize).write(n);
            for i in 0..n {
                (p.add(24 + i * PTR_SIZE) as *mut usize).write(self.tmp[i]);
            }
            self.save_max_sharing(o as usize, new_off, obj_sz);
            true
        }

        unsafe fn insert_sarray(&mut self, o: *mut LeanObject) {
            let elem_sz = (*o).other as usize;
            let n = (*(o as *const LeanScalarArray)).size;
            let obj_sz = core::mem::size_of::<LeanScalarArray>() + elem_sz * n;
            let new_off = self.alloc(obj_sz);
            self.set_non_heap_header_for_big(new_off, LEAN_SCALAR_ARRAY_TAG, elem_sz as u8);
            let p = self.buf.as_mut_ptr().add(new_off);
            (p.add(8) as *mut usize).write(n);
            (p.add(16) as *mut usize).write(n);
            core::ptr::copy_nonoverlapping((o as *const u8).add(24), p.add(24), elem_sz * n);
            self.save_max_sharing(o as usize, new_off, obj_sz);
        }

        unsafe fn insert_string(&mut self, o: *mut LeanObject) {
            let s = o as *const LeanStringObject;
            let size = (*s).size;
            let len = (*s).len;
            let obj_sz = core::mem::size_of::<LeanStringObject>() + size;
            let new_off = self.alloc(obj_sz);
            self.set_non_heap_header_for_big(new_off, LEAN_STRING_TAG, 0);
            let p = self.buf.as_mut_ptr().add(new_off);
            (p.add(8) as *mut usize).write(size);
            (p.add(16) as *mut usize).write(size);
            (p.add(24) as *mut usize).write(len);
            core::ptr::copy_nonoverlapping((o as *const u8).add(32), p.add(32), size);
            self.save_max_sharing(o as usize, new_off, obj_sz);
        }

        unsafe fn insert_thunk(&mut self, o: *mut LeanObject) -> bool {
            match self.to_offset(thunk_get_borrow(o)) {
                None => false,
                Some(c) => {
                    let new_off = self.copy_object(o);
                    (self.buf.as_mut_ptr().add(new_off + LEAN_VALUE_OFFSET) as *mut usize).write(c);
                    let sz = runtime_object_size_impl::lean_object_byte_size(o);
                    self.save_max_sharing(o as usize, new_off, sz);
                    true
                }
            }
        }

        unsafe fn insert_ref(&mut self, o: *mut LeanObject) -> bool {
            let v = (o as *const u8)
                .add(LEAN_VALUE_OFFSET)
                .cast::<*mut LeanObject>()
                .read();
            match self.to_offset(v) {
                None => false,
                Some(c) => {
                    let new_off = self.copy_object(o);
                    (self.buf.as_mut_ptr().add(new_off + LEAN_VALUE_OFFSET) as *mut usize).write(c);
                    let sz = runtime_object_size_impl::lean_object_byte_size(o);
                    self.save_max_sharing(o as usize, new_off, sz);
                    true
                }
            }
        }

        unsafe fn insert_task(&mut self, o: *mut LeanObject) -> bool {
            // lean_task_get blocks until complete (borrowed result, m_imp becomes null)
            match self.to_offset(lean_task_get(o)) {
                None => false,
                Some(c) => {
                    let new_off = self.copy_object(o);
                    (self.buf.as_mut_ptr().add(new_off + LEAN_VALUE_OFFSET) as *mut usize).write(c);
                    // m_imp (offset 16) is null after lean_task_get; copy_object preserved it
                    let sz = runtime_object_size_impl::lean_object_byte_size(o);
                    self.save_max_sharing(o as usize, new_off, sz);
                    true
                }
            }
        }

        unsafe fn insert_promise(&mut self, o: *mut LeanObject) -> bool {
            let m_result = (o as *const u8)
                .add(LEAN_VALUE_OFFSET)
                .cast::<*mut LeanObject>()
                .read();
            match self.to_offset(m_result) {
                None => false,
                Some(c) => {
                    let new_off = self.copy_object(o);
                    (self.buf.as_mut_ptr().add(new_off + LEAN_VALUE_OFFSET) as *mut usize).write(c);
                    let sz = runtime_object_size_impl::lean_object_byte_size(o);
                    self.save_max_sharing(o as usize, new_off, sz);
                    true
                }
            }
        }

        unsafe fn insert_closure(
            &mut self,
            o: *mut LeanObject,
        ) -> Result<bool, std::string::String> {
            if !self.allow_closures {
                return Err("Closures cannot be compacted (unless explicitly calling \
                     `CompactedRegion.save (allowClosures := true)`). \
                     One possible cause of this error is trying to store a function \
                     in a persistent environment extension."
                    .to_owned());
            }
            let num_fixed = (o as *const u8)
                .add(LEAN_CLOSURE_NUM_FIXED_OFFSET)
                .cast::<u16>()
                .read_unaligned() as usize;
            self.tmp.resize(num_fixed, 0);
            let mut missing = false;
            let mut i = num_fixed;
            while i > 0 {
                i -= 1;
                let child = (o as *const u8)
                    .add(LEAN_CLOSURE_ARGS_OFFSET + i * PTR_SIZE)
                    .cast::<*mut LeanObject>()
                    .read();
                match self.to_offset(child) {
                    Some(off) => self.tmp[i] = off,
                    None => missing = true,
                }
            }
            if missing {
                return Ok(false);
            }
            let new_off = self.copy_object(o);
            let p = self.buf.as_mut_ptr().add(new_off);
            for i in 0..num_fixed {
                (p.add(LEAN_CLOSURE_ARGS_OFFSET + i * PTR_SIZE) as *mut usize).write(self.tmp[i]);
            }
            // Record m_fun field offset for closure fn-ptr relocation on load
            self.closure_offsets.push(new_off + LEAN_CLOSURE_FUN_OFFSET);
            // Closures are unique (fn ptrs differ); use save, not save_max_sharing
            self.save(o as usize, new_off);
            Ok(true)
        }

        #[cfg(lean_use_gmp)]
        unsafe fn insert_mpz(&mut self, o: *mut LeanObject) {
            let mp_size_raw = (o as *const u8)
                .add(LEAN_MPZ_MP_SIZE_OFFSET)
                .cast::<i32>()
                .read();
            let nlimbs = mp_size_raw.unsigned_abs() as usize;
            let data_sz = nlimbs * LEAN_MP_LIMB_SIZE;
            let sz = LEAN_MPZ_OBJECT_SIZE + data_sz;
            let new_off = self.alloc(sz);
            core::ptr::copy_nonoverlapping(
                o as *const u8,
                self.buf.as_mut_ptr().add(new_off),
                LEAN_MPZ_OBJECT_SIZE,
            );
            self.set_non_heap_header(new_off, sz as u16, LEAN_MPZ_TAG, 0);
            // Copy limb data from original's _mp_d pointer
            let orig_mp_d = (o as *const u8)
                .add(LEAN_MPZ_MP_D_OFFSET)
                .cast::<*const u8>()
                .read();
            let limbs_off = new_off + LEAN_MPZ_OBJECT_SIZE;
            core::ptr::copy_nonoverlapping(
                orig_mp_d,
                self.buf.as_mut_ptr().add(limbs_off),
                data_sz,
            );
            // Patch _mp_d to base_addr-relative pointer
            (self.buf.as_mut_ptr().add(new_off + LEAN_MPZ_MP_D_OFFSET) as *mut usize)
                .write(self.base_addr + limbs_off);
            // Set _mp_alloc = nlimbs
            (self
                .buf
                .as_mut_ptr()
                .add(new_off + LEAN_MPZ_MP_ALLOC_OFFSET) as *mut i32)
                .write(nlimbs as i32);
            self.save(o as usize, new_off);
        }

        #[cfg(not(lean_use_gmp))]
        unsafe fn insert_mpz(&mut self, o: *mut LeanObject) {
            let m_size = (o as *const u8)
                .add(LEAN_MPZ_SIZE_OFFSET)
                .cast::<usize>()
                .read();
            let data_sz = m_size * LEAN_MPN_DIGIT_SIZE;
            let sz = LEAN_MPZ_OBJECT_SIZE + data_sz;
            let new_off = self.alloc(sz);
            let p = self.buf.as_mut_ptr().add(new_off);
            // Manually copy only meaningful fields to leave padding as zero
            core::ptr::copy_nonoverlapping(o as *const u8, p, 8); // m_header
            *p.add(LEAN_MPZ_SIGN_OFFSET) = *(o as *const u8).add(LEAN_MPZ_SIGN_OFFSET);
            (p.add(LEAN_MPZ_SIZE_OFFSET) as *mut usize).write(m_size);
            self.set_non_heap_header(new_off, sz as u16, LEAN_MPZ_TAG, 0);
            // Copy digit data from original's m_digits pointer
            let orig_digits = (o as *const u8)
                .add(LEAN_MPZ_DIGITS_OFFSET)
                .cast::<*const u8>()
                .read();
            let digits_off = new_off + LEAN_MPZ_OBJECT_SIZE;
            core::ptr::copy_nonoverlapping(orig_digits, p.add(LEAN_MPZ_OBJECT_SIZE), data_sz);
            // Patch m_digits to base_addr-relative pointer
            (p.add(LEAN_MPZ_DIGITS_OFFSET) as *mut usize).write(self.base_addr + digits_off);
            self.save(o as usize, new_off);
        }

        /// DFS-serialize odata into buf via LIFO todo stack.
        unsafe fn compact(&mut self, odata: *mut LeanObject) -> Result<(), std::string::String> {
            debug_assert!(self.todo.is_empty());
            let root_slot = self.alloc(PTR_SIZE);

            if !lean_is_scalar(odata) {
                self.todo.push(odata);
                while let Some(&curr) = self.todo.last() {
                    if self.obj_table.contains_key(&(curr as usize)) {
                        self.todo.pop();
                        continue;
                    }
                    let tag = (*curr).tag;
                    let done = if tag <= LEAN_MAX_CTOR_TAG {
                        self.insert_constructor(curr)
                    } else {
                        match tag {
                            LEAN_CLOSURE_TAG => self.insert_closure(curr)?,
                            LEAN_ARRAY_TAG => self.insert_array(curr),
                            LEAN_SCALAR_ARRAY_TAG => {
                                self.insert_sarray(curr);
                                true
                            }
                            LEAN_STRING_TAG => {
                                self.insert_string(curr);
                                true
                            }
                            LEAN_MPZ_TAG => {
                                self.insert_mpz(curr);
                                true
                            }
                            LEAN_THUNK_TAG => self.insert_thunk(curr),
                            LEAN_TASK_TAG => self.insert_task(curr),
                            LEAN_PROMISE_TAG => self.insert_promise(curr),
                            LEAN_REF_TAG => self.insert_ref(curr),
                            LEAN_EXTERNAL_TAG => {
                                return Err("external objects cannot be compacted".to_owned());
                            }
                            _ => return Err(format!("unexpected lean object tag: {}", tag)),
                        }
                    };
                    if done {
                        self.todo.pop();
                    }
                }
                self.tmp.clear();
            }

            let root_addr = self.to_offset(odata).unwrap_or(0);
            (self.buf.as_mut_ptr().add(root_slot) as *mut usize).write(root_addr);
            Ok(())
        }

        /// Return indices into self.libs of libraries containing a recorded closure fn ptr.
        fn used_lib_indices(&self) -> Vec<usize> {
            let mut used = vec![false; self.libs.len()];
            for &off in &self.closure_offsets {
                let fn_ptr = unsafe { (self.buf.as_ptr().add(off) as *const usize).read() };
                let idx = self.libs.partition_point(|l| l.base_addr <= fn_ptr);
                if idx > 0 {
                    used[idx - 1] = true;
                }
            }
            (0..self.libs.len()).filter(|&i| used[i]).collect()
        }
    }

    // -------------------------------------------------------------------------
    // OLEAN header builder
    // -------------------------------------------------------------------------

    unsafe extern "C" {
        fn lean_short_version_string() -> *const c_char;
    }

    fn build_olean_header(version: u8, base_addr: usize) -> [u8; OLEAN_HEADER_SIZE] {
        let mut h = [0u8; OLEAN_HEADER_SIZE];
        h[..5].copy_from_slice(OLEAN_MARKER);
        h[5] = version;
        h[6] = OLEAN_FLAGS_GMP;
        let ver = unsafe { CStr::from_ptr(lean_short_version_string()).to_bytes() };
        let vlen = ver.len().min(33);
        h[7..7 + vlen].copy_from_slice(&ver[..vlen]);
        let gh = LEAN_GITHASH.as_bytes();
        let glen = gh.len().min(40);
        h[40..40 + glen].copy_from_slice(&gh[..glen]);
        h[80..80 + PTR_SIZE].copy_from_slice(&base_addr.to_ne_bytes());
        h
    }

    // -------------------------------------------------------------------------
    // Compactor external class
    // -------------------------------------------------------------------------

    static COMPACTOR_CLASS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();

    unsafe fn compactor_finalizer(data: *mut c_void) {
        drop(Box::from_raw(data as *mut ObjectCompactor));
    }

    unsafe fn compactor_foreach(_data: *mut c_void, _o: *mut LeanObject) {}

    fn get_compactor_class() -> *mut LeanExternalClass {
        *COMPACTOR_CLASS.get_or_init(|| unsafe {
            lean_register_external_class(Some(compactor_finalizer), Some(compactor_foreach))
                as usize
        }) as *mut LeanExternalClass
    }

    // -------------------------------------------------------------------------
    // File writing
    // -------------------------------------------------------------------------

    unsafe fn write_olean(
        _olean_fn: &str,
        olean_tmp_fn: &str,
        compactor: &mut ObjectCompactor,
        file_offset: usize,
        odata: *mut LeanObject,
        allow_closures: bool,
    ) -> Result<(), std::string::String> {
        let version = if allow_closures {
            OLEAN_VERSION_V3
        } else {
            OLEAN_VERSION_V2
        };
        let base_addr_for_file = compactor.base_addr + file_offset;
        let header = build_olean_header(version, base_addr_for_file);

        let file = std::fs::File::create(olean_tmp_fn)
            .map_err(|e| format!("failed to create '{}': {}", olean_tmp_fn, e))?;
        let mut out = std::io::BufWriter::new(file);

        out.write_all(&header).map_err(|e| e.to_string())?;

        if !allow_closures {
            // v2: [header(88)][data]
            let data_start = file_offset + OLEAN_HEADER_SIZE;
            compactor.compact(odata)?;
            out.write_all(&compactor.buf[data_start..])
                .map_err(|e| e.to_string())?;
        } else {
            // v3: [header(88)][data_size(8)][data][num_co(4)][co_offsets(8*n)][lib_table]
            let data_offset = file_offset + OLEAN_HEADER_SIZE + PTR_SIZE;
            compactor.compact(odata)?;
            let data_size = compactor.buf.len() - data_offset;

            out.write_all(&data_size.to_ne_bytes())
                .map_err(|e| e.to_string())?;
            out.write_all(&compactor.buf[data_offset..])
                .map_err(|e| e.to_string())?;

            // Gather closure offsets (data-section-relative) and used libs before clearing
            let used_indices = compactor.used_lib_indices();
            let file_offsets: Vec<u64> = compactor
                .closure_offsets
                .iter()
                .map(|&off| (off - data_offset) as u64)
                .collect();
            // Snapshot used lib data (base_addr + id) before any alloc that could move buf
            struct SnapLib {
                base_addr: usize,
                id: Vec<u8>,
            }
            let snap_libs: Vec<SnapLib> = used_indices
                .iter()
                .map(|&i| SnapLib {
                    base_addr: compactor.libs[i].base_addr,
                    id: compactor.libs[i].id.as_bytes().to_vec(),
                })
                .collect();
            compactor.closure_offsets.clear();

            // Reserve trailer bytes in compactor buf (so future saves have correct offsets)
            let num_co = file_offsets.len() as u32;
            let lt_sz = core::mem::size_of::<u32>()
                + snap_libs
                    .iter()
                    .map(|l| PTR_SIZE + core::mem::size_of::<u32>() + l.id.len())
                    .sum::<usize>();
            let trailer_sz = core::mem::size_of::<u32>() + file_offsets.len() * 8 + lt_sz;
            compactor.alloc(trailer_sz);

            // Write trailer to file
            out.write_all(&num_co.to_ne_bytes())
                .map_err(|e| e.to_string())?;
            for &co in &file_offsets {
                out.write_all(&co.to_ne_bytes())
                    .map_err(|e| e.to_string())?;
            }
            let num_libs = snap_libs.len() as u32;
            out.write_all(&num_libs.to_ne_bytes())
                .map_err(|e| e.to_string())?;
            for lib in &snap_libs {
                out.write_all(&lib.base_addr.to_ne_bytes())
                    .map_err(|e| e.to_string())?;
                out.write_all(&(lib.id.len() as u32).to_ne_bytes())
                    .map_err(|e| e.to_string())?;
                out.write_all(&lib.id).map_err(|e| e.to_string())?;
            }
        }

        out.flush().map_err(|e| e.to_string())?;
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Public FFI entry point
    // -------------------------------------------------------------------------

    /// Port of `lean_cxx_compacted_region_save` from src/library/module.cpp.
    ///
    /// Lean signature:
    ///   CompactedRegion.save (fname : @& FilePath) (key : @& Name)
    ///       (data : @& α) (depRegions : @& Array CompactedRegion)
    ///       (prev : Option Compactor) (allowClosures := false) : IO Compactor
    #[no_mangle]
    pub unsafe fn lean_compacted_region_save(
        ofname: *mut LeanObject,
        mod_: *mut LeanObject,
        odata: *mut LeanObject,
        odep_regions: *mut LeanObject,
        oprev: *mut LeanObject,
        allow_closures: u8,
        _io: *mut LeanObject,
    ) -> *mut LeanObject {
        let allow_closures = allow_closures != 0;

        // ---- Extract or create the compactor ----
        let cs_obj = if lean_is_scalar(oprev) {
            let hash = lean_name_hash_val(mod_);
            let base_addr = (hash as usize % 0x7f_0000_0000_00) & !(PAGE_ALIGN - 1);
            let dep_regions = extract_dep_regions_for_writer(odep_regions);
            let libs = get_loaded_libs();
            let compactor = Box::new(ObjectCompactor::new(
                base_addr,
                dep_regions,
                allow_closures,
                libs,
            ));
            lean_runtime_alloc_external(
                get_compactor_class(),
                Box::into_raw(compactor) as *mut c_void,
            )
        } else {
            // prev = Some(inner): reuse existing; inc inner before dec'ing Some wrapper
            let inner = lean_ctor_get(oprev, 0);
            lean_inc(inner);
            lean_dec(oprev);
            inner
        };

        let compactor = &mut *(lean_runtime_get_external_data(cs_obj) as *mut ObjectCompactor);

        // ---- Build paths ----
        let olean_fn_cstr = lean_string_cstr(ofname);
        let olean_fn = CStr::from_ptr(olean_fn_cstr).to_string_lossy().into_owned();
        let pid = libc::getpid() as u32;
        let olean_tmp_fn = format!("{}.tmp.{}", olean_fn, pid);

        // ---- Align buffer to PAGE_ALIGN ----
        let cur_size = compactor.buf.len();
        let rem = cur_size % PAGE_ALIGN;
        if rem != 0 {
            compactor.alloc(PAGE_ALIGN - rem);
        }
        let file_offset = compactor.buf.len();

        // Reserve space for the olean header (and data_size slot for v3) so that
        // subsequent object offsets account for the header in the file.
        let header_reserve = if allow_closures {
            OLEAN_HEADER_SIZE + PTR_SIZE
        } else {
            OLEAN_HEADER_SIZE
        };
        compactor.alloc(header_reserve);

        // ---- Write file ----
        let result = write_olean(
            &olean_fn,
            &olean_tmp_fn,
            compactor,
            file_offset,
            odata,
            allow_closures,
        );

        if let Err(msg) = result {
            let _ = std::fs::remove_file(&olean_tmp_fn);
            lean_dec(cs_obj);
            let full_msg = format!("failed to write '{}': {}", olean_fn, msg);
            let cstr = std::ffi::CString::new(full_msg)
                .unwrap_or_else(|_| std::ffi::CString::new("write error").unwrap());
            let msg_obj = lean_mk_string(cstr.as_ptr());
            let err = lean_mk_io_user_error(msg_obj);
            return lean_io_result_mk_error(err);
        }

        // ---- Atomic rename ----
        if let Err(e) = std::fs::rename(&olean_tmp_fn, &olean_fn) {
            let _ = std::fs::remove_file(&olean_tmp_fn);
            lean_dec(cs_obj);
            let full_msg = format!("failed to write '{}': {}", olean_fn, e);
            let cstr = std::ffi::CString::new(full_msg)
                .unwrap_or_else(|_| std::ffi::CString::new("rename error").unwrap());
            let msg_obj = lean_mk_string(cstr.as_ptr());
            let err = lean_mk_io_user_error(msg_obj);
            return lean_io_result_mk_error(err);
        }

        lean_io_result_mk_ok(cs_obj)
    }
}
