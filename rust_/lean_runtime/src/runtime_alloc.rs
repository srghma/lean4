// Port of src/runtime/alloc.cpp
// Copyright (c) 2019 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// When LEAN_SMALL_ALLOCATOR is enabled (feature "small_allocator") this
// implements the full page/segment/heap slab allocator that matches the C++
// design exactly: same constants, same page-header layout, same cross-thread
// export/import protocol, same heartbeat counter.
//
// When the feature is disabled the functions fall through to the system
// allocator (libc malloc) via the lean.h inline helpers.

mod runtime_alloc_impl {
    use std::cell::Cell;

    // -----------------------------------------------------------------------
    // Constants (must match lean.h / alloc.cpp exactly)
    // -----------------------------------------------------------------------

    const LEAN_PAGE_SIZE: usize = 8192; // 8 KB
    const LEAN_SEGMENT_SIZE: usize = 8 * 1024 * 1024; // 8 MB
    const LEAN_OBJECT_SIZE_DELTA: usize = 8; // alignment quantum
    const LEAN_MAX_SMALL_OBJECT_SIZE: usize = 512; // from lean.h
    const LEAN_NUM_SLOTS: usize = LEAN_MAX_SMALL_OBJECT_SIZE / LEAN_OBJECT_SIZE_DELTA;
    const LEAN_MAX_TO_EXPORT_OBJS: usize = 1024;

    // -----------------------------------------------------------------------
    // Helpers mirroring lean.h macros
    // -----------------------------------------------------------------------

    #[inline(always)]
    fn lean_align(sz: usize, delta: usize) -> usize {
        (sz + delta - 1) & !(delta - 1)
    }

    #[inline(always)]
    fn lean_get_slot_idx(sz: usize) -> usize {
        // sz is already aligned to LEAN_OBJECT_SIZE_DELTA
        sz / LEAN_OBJECT_SIZE_DELTA - 1
    }

    // -----------------------------------------------------------------------
    // External allocator primitives from lean.h / system allocator
    // -----------------------------------------------------------------------

    extern "C" {
        fn lean_internal_panic_out_of_memory() -> !;
    }

    // -----------------------------------------------------------------------
    // Small allocator (feature = "small_allocator")
    // -----------------------------------------------------------------------

    #[cfg(feature = "small_allocator")]
    mod small_alloc {
        use super::*;
        use core::sync::atomic::{AtomicPtr, Ordering};
        use std::sync::Mutex;

        // ------------------------------------------------------------------
        // Page header — must match the C++ `page_header` struct layout.
        // We use raw pointer arithmetic so the layout must be byte-exact.
        // ------------------------------------------------------------------

        /// Per-page metadata, placed at the very start of each page-aligned
        /// 8 KB region. The `m_data` area that follows immediately after is
        /// used for objects.
        #[repr(C)]
        struct PageHeader {
            /// Owning heap (atomic because other threads read it during dealloc).
            m_heap: AtomicPtr<Heap>,
            m_next: *mut Page,
            m_prev: *mut Page,
            m_free_list: *mut u8,
            m_obj_size: u32,
            m_max_free: u32,
            m_num_free: u32,
            m_slot_idx: u32,
            m_in_page_free_list: bool,
        }

        #[repr(C)]
        struct Page {
            m_header: PageHeader,
            // m_data follows immediately — size = LEAN_PAGE_SIZE - sizeof(PageHeader)
        }

        impl Page {
            #[inline]
            fn data_start(&mut self) -> *mut u8 {
                // Data begins right after the header.
                unsafe {
                    (self as *mut Page as *mut u8)
                        .add(core::mem::size_of::<PageHeader>())
                }
            }

            #[inline]
            fn has_many_free(&self) -> bool {
                self.m_header.m_num_free > self.m_header.m_max_free / 4
            }

            #[inline]
            fn push_free_obj(&mut self, o: *mut u8, heap: *mut Heap) {
                set_next_obj(o, self.m_header.m_free_list);
                self.m_header.m_free_list = o;
                self.m_header.m_num_free += 1;
                let slot_idx = self.m_header.m_slot_idx as usize;
                if !self.m_header.m_in_page_free_list && self.has_many_free() {
                    unsafe {
                        let curr_page = (*heap).m_curr_page[slot_idx];
                        if self as *mut Page != curr_page {
                            self.m_header.m_in_page_free_list = true;
                            page_list_remove(&mut (*heap).m_curr_page[slot_idx], self);
                            page_list_insert(&mut (*heap).m_page_free_list[slot_idx], self);
                        }
                    }
                }
            }
        }

        // ------------------------------------------------------------------
        // Segment — 8 MB allocation arena, page-aligned
        // ------------------------------------------------------------------

        #[repr(C)]
        struct Segment {
            m_next: *mut Segment,
            m_next_page_mem: *mut u8,
            // 8 MB of data follows (allocated via mmap/VirtualAlloc)
        }

        impl Segment {
            /// Allocates a new segment (8 MB anonymous mmap / VirtualAlloc).
            unsafe fn alloc() -> *mut Segment {
                let layout = std::alloc::Layout::from_size_align(
                    LEAN_SEGMENT_SIZE + LEAN_PAGE_SIZE, // extra for page alignment
                    LEAN_PAGE_SIZE,
                )
                .expect("segment layout");
                let raw = std::alloc::alloc_zeroed(layout);
                if raw.is_null() {
                    lean_internal_panic_out_of_memory()
                }
                let seg = raw as *mut Segment;
                (*seg).m_next = core::ptr::null_mut();
                // first page_mem starts at the first page-aligned address after
                // the Segment header
                let header_end = raw.add(core::mem::size_of::<Segment>());
                let aligned = lean_align(header_end as usize, LEAN_PAGE_SIZE) as *mut u8;
                (*seg).m_next_page_mem = aligned;
                seg
            }

            unsafe fn dealloc(seg: *mut Segment) {
                let layout = std::alloc::Layout::from_size_align(
                    LEAN_SEGMENT_SIZE + LEAN_PAGE_SIZE,
                    LEAN_PAGE_SIZE,
                )
                .unwrap();
                std::alloc::dealloc(seg as *mut u8, layout);
            }

            unsafe fn is_full(&self) -> bool {
                self.m_next_page_mem.add(LEAN_PAGE_SIZE)
                    > (self as *const Segment as *mut u8)
                        .add(LEAN_SEGMENT_SIZE + LEAN_PAGE_SIZE)
            }
        }

        // ------------------------------------------------------------------
        // Per-thread Heap
        // ------------------------------------------------------------------

        #[repr(C)]
        struct Heap {
            m_curr_segment: *mut Segment,
            m_next_orphan: *mut Heap,
            m_curr_page: [*mut Page; LEAN_NUM_SLOTS],
            m_page_free_list: [*mut Page; LEAN_NUM_SLOTS],
            // Objects to be sent to other heaps (collected before export)
            m_to_export_list: *mut u8,
            m_to_export_list_size: usize,
            // Mutex-protected import list
            m_mutex: Mutex<*mut u8>,
            /// Heartbeat counter — incremented on every small allocation.
            pub m_heartbeat: u64,
        }

        impl Heap {
            unsafe fn new() -> *mut Heap {
                let layout =
                    std::alloc::Layout::new::<Heap>();
                let raw = std::alloc::alloc_zeroed(layout) as *mut Heap;
                if raw.is_null() {
                    lean_internal_panic_out_of_memory()
                }
                // Initialize mutex via ptr::write to avoid MaybeUninit issues
                core::ptr::write(&mut (*raw).m_mutex, Mutex::new(core::ptr::null_mut()));
                raw
            }

            unsafe fn import_objs(&mut self) {
                let to_import = {
                    let mut guard = self.m_mutex.lock().unwrap();
                    let ptr = *guard;
                    *guard = core::ptr::null_mut();
                    ptr
                };
                let mut cur = to_import;
                while !cur.is_null() {
                    let page = get_page_of(cur);
                    let next = get_next_obj(cur);
                    (*page).push_free_obj(cur, self as *mut Heap);
                    cur = next;
                }
            }

            unsafe fn export_objs(&mut self) {
                // Group objects by their owning heap, then bulk-prepend each group
                // to the target heap's import list.
                struct Entry {
                    heap: *mut Heap,
                    head: *mut u8,
                    tail: *mut u8,
                }
                let mut to_export: Vec<Entry> = Vec::new();
                let mut o = self.m_to_export_list;
                while !o.is_null() {
                    let next = get_next_obj(o);
                    let h = (*get_page_of(o)).m_header.m_heap.load(Ordering::Relaxed);
                    let mut found = false;
                    for e in &mut to_export {
                        if e.heap == h {
                            set_next_obj(o, e.head);
                            e.head = o;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        set_next_obj(o, core::ptr::null_mut());
                        to_export.push(Entry { heap: h, head: o, tail: o });
                    }
                    o = next;
                }
                self.m_to_export_list = core::ptr::null_mut();
                self.m_to_export_list_size = 0;
                for e in to_export {
                    let mut guard = (*e.heap).m_mutex.lock().unwrap();
                    set_next_obj(e.tail, *guard);
                    *guard = e.head;
                }
            }

            unsafe fn alloc_segment(&mut self) {
                let s = Segment::alloc();
                (*s).m_next = self.m_curr_segment;
                self.m_curr_segment = s;
            }
        }

        // ------------------------------------------------------------------
        // Global heap manager (orphan pool for thread reuse)
        // ------------------------------------------------------------------

        struct HeapManager {
            m_mutex: Mutex<*mut Heap>,
        }

        unsafe impl Send for HeapManager {}
        unsafe impl Sync for HeapManager {}

        impl HeapManager {
            const fn new() -> Self {
                HeapManager { m_mutex: Mutex::new(core::ptr::null_mut()) }
            }

            unsafe fn push_orphan(&self, h: *mut Heap) {
                let mut guard = self.m_mutex.lock().unwrap();
                (*h).m_next_orphan = *guard;
                *guard = h;
            }

            unsafe fn pop_orphan(&self) -> *mut Heap {
                let mut guard = self.m_mutex.lock().unwrap();
                let h = *guard;
                if !h.is_null() {
                    *guard = (*h).m_next_orphan;
                }
                h
            }
        }

        static G_HEAP_MANAGER: HeapManager = HeapManager::new();

        // ------------------------------------------------------------------
        // Thread-local heap pointer
        // ------------------------------------------------------------------

        thread_local! {
            static G_HEAP: Cell<*mut Heap> = const { Cell::new(core::ptr::null_mut()) };
            // Mirror of g_curr_pages — pointer into G_HEAP.m_curr_page array
            // used by the hot path.
            static G_CURR_PAGES: Cell<*mut [*mut Page; LEAN_NUM_SLOTS]> =
                const { Cell::new(core::ptr::null_mut()) };
        }

        #[inline(always)]
        unsafe fn get_heap() -> *mut Heap {
            G_HEAP.with(|c| c.get())
        }

        #[inline(always)]
        unsafe fn get_curr_pages() -> *mut [*mut Page; LEAN_NUM_SLOTS] {
            G_CURR_PAGES.with(|c| c.get())
        }

        // ------------------------------------------------------------------
        // Page linked-list helpers
        // ------------------------------------------------------------------

        #[inline]
        unsafe fn page_list_insert(head: &mut *mut Page, new_head: *mut Page) {
            if !(*head).is_null() {
                (**head).m_header.m_prev = new_head;
            }
            (*new_head).m_header.m_next = *head;
            (*new_head).m_header.m_prev = core::ptr::null_mut();
            *head = new_head;
        }

        #[inline]
        unsafe fn page_list_remove(head: &mut *mut Page, to_remove: *mut Page) {
            if *head == to_remove {
                *head = (*to_remove).m_header.m_next;
            }
            let prev = (*to_remove).m_header.m_prev;
            if !prev.is_null() {
                (*prev).m_header.m_next = (*to_remove).m_header.m_next;
            }
            if let Some(next) = (*to_remove).m_header.m_next.as_mut() {
                next.m_header.m_prev = prev;
            }
        }

        #[inline]
        unsafe fn page_list_pop(head: &mut *mut Page) -> *mut Page {
            let r = *head;
            *head = (*r).m_header.m_next;
            r
        }

        // ------------------------------------------------------------------
        // Free-list pointer packing in objects
        // ------------------------------------------------------------------

        #[inline(always)]
        unsafe fn set_next_obj(obj: *mut u8, next: *mut u8) {
            *(obj as *mut *mut u8) = next;
        }

        #[inline(always)]
        unsafe fn get_next_obj(obj: *mut u8) -> *mut u8 {
            *(obj as *mut *mut u8)
        }

        // ------------------------------------------------------------------
        // Page-of lookup: round down to page alignment
        // ------------------------------------------------------------------

        #[inline(always)]
        unsafe fn get_page_of(o: *mut u8) -> *mut Page {
            let addr = o as usize;
            let page_addr = (addr / LEAN_PAGE_SIZE) * LEAN_PAGE_SIZE;
            page_addr as *mut Page
        }

        // ------------------------------------------------------------------
        // Allocate a new page within a heap for the given object size
        // ------------------------------------------------------------------

        unsafe fn alloc_page(h: *mut Heap, obj_size: usize) -> *mut Page {
            let s = (*h).m_curr_segment;
            let p = (*s).m_next_page_mem as *mut Page;
            (*s).m_next_page_mem = (*s).m_next_page_mem.add(LEAN_PAGE_SIZE);

            if (*s).is_full() {
                (*h).alloc_segment();
            }

            let slot_idx = lean_get_slot_idx(obj_size);
            (*p).m_header.m_heap = AtomicPtr::new(h);
            (*p).m_header.m_next = core::ptr::null_mut();
            (*p).m_header.m_prev = core::ptr::null_mut();
            (*p).m_header.m_slot_idx = slot_idx as u32;
            (*p).m_header.m_obj_size = obj_size as u32;
            (*p).m_header.m_in_page_free_list = false;

            page_list_insert(&mut (*h).m_curr_page[slot_idx], p);

            // Build the free list from data area
            let data_start = (*p).data_start();
            let data_end = (p as *mut u8).add(LEAN_PAGE_SIZE);
            let available = data_end as usize - data_start as usize;
            let num_free = (available / obj_size) as u32;

            // Link objects: last object points to null, each subsequent points to previous
            let mut curr = data_start;
            set_next_obj(curr, core::ptr::null_mut());
            let mut prev = curr;
            curr = curr.add(obj_size);
            let mut count = 1u32;
            while curr.add(obj_size) <= data_end {
                set_next_obj(curr, prev);
                prev = curr;
                curr = curr.add(obj_size);
                count += 1;
            }
            (*p).m_header.m_free_list = prev; // head of free list (last-allocated = highest addr)
            (*p).m_header.m_max_free = count;
            (*p).m_header.m_num_free = count;
            let _ = num_free; // suppress unused warning

            p
        }

        // ------------------------------------------------------------------
        // Thread heap finalizer — called when a thread exits
        // ------------------------------------------------------------------

        unsafe fn finalize_heap(h: *mut Heap) {
            (*h).export_objs();
            (*h).import_objs();
            G_HEAP_MANAGER.push_orphan(h);
        }

        extern "C" fn finalize_heap_c(data: *mut core::ffi::c_void) {
            unsafe { finalize_heap(data as *mut Heap) }
        }

        // ------------------------------------------------------------------
        // Initialize a thread's heap (called on first alloc or explicitly)
        // ------------------------------------------------------------------

        #[cold]
        unsafe fn init_heap(main: bool) {
            assert!(get_heap().is_null());
            let h = if let Some(orphan) = G_HEAP_MANAGER.pop_orphan().as_mut() {
                orphan as *mut Heap
            } else {
                let h = Heap::new();
                G_CURR_PAGES.with(|c| c.set(&mut (*h).m_curr_page as *mut _));
                for i in 0..LEAN_NUM_SLOTS {
                    (*h).m_curr_page[i] = core::ptr::null_mut();
                    (*h).m_page_free_list[i] = core::ptr::null_mut();
                }
                (*h).alloc_segment();
                // Pre-populate one page per slot
                let mut obj_size = LEAN_OBJECT_SIZE_DELTA;
                for i in 0..LEAN_NUM_SLOTS {
                    if (*h).m_curr_page[i].is_null() {
                        alloc_page(h, obj_size);
                    }
                    obj_size += LEAN_OBJECT_SIZE_DELTA;
                }
                h
            };
            G_HEAP.with(|c| c.set(h));
            if !main {
                super::super::register_thread_finalizer(finalize_heap_c, h as *mut core::ffi::c_void);
            }
        }

        // ------------------------------------------------------------------
        // Public: init_thread_heap  (called from lean_initialize_thread)
        // ------------------------------------------------------------------

        pub unsafe fn init_thread_heap() {
            init_heap(false);
        }

        // ------------------------------------------------------------------
        // Cold path for lean_alloc_small
        // ------------------------------------------------------------------

        #[cold]
        pub unsafe fn lean_alloc_small_cold(
            sz: usize,
            slot_idx: usize,
            p: *mut Page,
        ) -> *mut u8 {
            let h = get_heap();
            if (*h).m_page_free_list[slot_idx].is_null() {
                (*h).import_objs();
                // import_objs may have populated p's free list
                if (*p).m_header.m_free_list.is_null() {
                    let p2 = alloc_page(h, sz);
                    let r = (*p2).m_header.m_free_list;
                    (*p2).m_header.m_free_list = get_next_obj(r);
                    (*p2).m_header.m_num_free -= 1;
                    return r;
                }
            } else {
                let p2 = page_list_pop(&mut (*h).m_page_free_list[slot_idx]);
                (*p2).m_header.m_in_page_free_list = false;
                page_list_insert(&mut (*h).m_curr_page[slot_idx], p2);
                let r = (*p2).m_header.m_free_list;
                (*p2).m_header.m_free_list = get_next_obj(r);
                (*p2).m_header.m_num_free -= 1;
                return r;
            }
            // p now has objects (imported)
            let r = (*p).m_header.m_free_list;
            (*p).m_header.m_free_list = get_next_obj(r);
            (*p).m_header.m_num_free -= 1;
            r
        }

        // ------------------------------------------------------------------
        // lean_alloc_small — hot path
        // ------------------------------------------------------------------

        #[no_mangle]
        pub unsafe extern "C" fn lean_alloc_small(sz: u32, slot_idx: u32) -> *mut u8 {
            let h = get_heap();
            let slot = slot_idx as usize;
            (*h).m_heartbeat += 1;
            let p = (*h).m_curr_page[slot];
            let r = (*p).m_header.m_free_list;
            if r.is_null() {
                return lean_alloc_small_cold(sz as usize, slot, p);
            }
            (*p).m_header.m_free_list = get_next_obj(r);
            (*p).m_header.m_num_free -= 1;
            r
        }

        // ------------------------------------------------------------------
        // lean_free_small — return a small object to its page
        // ------------------------------------------------------------------

        #[cold]
        unsafe fn dealloc_small_cold(o: *mut u8) {
            let h = get_heap();
            (*h).m_to_export_list_size += 1;
            set_next_obj(o, (*h).m_to_export_list);
            (*h).m_to_export_list = o;
            if (*h).m_to_export_list_size > LEAN_MAX_TO_EXPORT_OBJS {
                (*h).export_objs();
            }
        }

        #[inline]
        unsafe fn dealloc_small_core(o: *mut u8) {
            let mut h = get_heap();
            if h.is_null() {
                init_heap(false);
                h = get_heap();
            }
            let p = get_page_of(o);
            if (*p).m_header.m_heap.load(Ordering::Relaxed) == h {
                (*p).push_free_obj(o, h);
            } else {
                dealloc_small_cold(o);
            }
        }

        #[no_mangle]
        pub unsafe extern "C" fn lean_free_small(o: *mut u8) {
            dealloc_small_core(o);
        }

        #[no_mangle]
        pub unsafe extern "C" fn lean_small_mem_size(o: *mut u8) -> u32 {
            let p = get_page_of(o);
            (*p).m_header.m_obj_size
        }

        // ------------------------------------------------------------------
        // alloc / dealloc  (C++ namespace lean functions)
        // ------------------------------------------------------------------

        /// `lean::alloc(sz)` — used internally by C++ runtime code.
        #[export_name = "_ZN4lean5allocEm"]
        pub unsafe extern "C" fn lean_alloc_export(sz: usize) -> *mut u8 {
            let sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
            if sz > LEAN_MAX_SMALL_OBJECT_SIZE {
                let r = lean_sys_alloc(sz);
                if r.is_null() {
                    lean_internal_panic_out_of_memory()
                }
                return r;
            }
            let slot_idx = lean_get_slot_idx(sz) as u32;
            lean_alloc_small(sz as u32, slot_idx)
        }

        /// `lean::dealloc(o, sz)` — used internally by C++ runtime code.
        #[export_name = "_ZN4lean7deallocEPvm"]
        pub unsafe extern "C" fn lean_dealloc_export(o: *mut u8, sz: usize) {
            let sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
            if sz > LEAN_MAX_SMALL_OBJECT_SIZE {
                lean_sys_free_sized(o, sz);
                return;
            }
            dealloc_small_core(o);
        }

        // ------------------------------------------------------------------
        // Heartbeat
        // ------------------------------------------------------------------

        pub unsafe fn set_heartbeats(count: u64) {
            let h = get_heap();
            if !h.is_null() {
                (*h).m_heartbeat = count;
            }
        }

        pub unsafe fn add_heartbeats(count: u64) {
            let h = get_heap();
            if !h.is_null() {
                (*h).m_heartbeat += count;
            }
        }

        pub unsafe fn get_num_heartbeats() -> u64 {
            let h = get_heap();
            if h.is_null() { 0 } else { (*h).m_heartbeat }
        }

        #[no_mangle]
        pub unsafe extern "C" fn lean_inc_heartbeat() {
            add_heartbeats(1);
        }

        #[no_mangle]
        pub unsafe extern "C" fn lean_get_num_heartbeats() -> u64 {
            get_num_heartbeats()
        }

        #[no_mangle]
        pub unsafe extern "C" fn lean_set_heartbeats(count: u64) {
            set_heartbeats(count);
        }

        // ------------------------------------------------------------------
        // Module init/finalize
        // ------------------------------------------------------------------

        pub unsafe fn initialize_alloc() {
            // The heap manager is a static — no heap allocation needed.
            // Initialize the main thread's heap.
            init_heap(true);
        }

        pub unsafe fn finalize_alloc() {
            // Nothing to do; segments are leaked intentionally (same as C++).
        }

        // ------------------------------------------------------------------
        // lean_initialize_thread hook (called from runtime_thread.rs)
        // ------------------------------------------------------------------

        #[no_mangle]
        pub unsafe extern "C" fn lean_small_alloc_initialize_thread() {
            init_thread_heap();
        }
    } // mod small_alloc

    // -----------------------------------------------------------------------
    // No-small-allocator path
    // -----------------------------------------------------------------------

    #[cfg(not(feature = "small_allocator"))]
    mod no_small_alloc {
        use super::*;
        use core::ffi::c_void;

        // lean_alloc_small / lean_free_small / lean_small_mem_size are defined
        // as inline functions in lean.h when LEAN_SMALL_ALLOCATOR is disabled.
        // We only need to provide the C++ namespace functions and heartbeat stubs.

        #[export_name = "_ZN4lean5allocEm"]
        pub unsafe extern "C" fn lean_alloc_export(sz: usize) -> *mut u8 {
            let sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
            let r = lean_sys_alloc(sz);
            if r.is_null() {
                lean_internal_panic_out_of_memory()
            }
            r
        }

        #[export_name = "_ZN4lean7deallocEPvm"]
        pub unsafe extern "C" fn lean_dealloc_export(o: *mut u8, sz: usize) {
            let sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
            lean_sys_free_sized(o, sz);
        }

        // Heartbeat stubs — no per-thread heap so heartbeats are unavailable.
        #[no_mangle]
        pub unsafe extern "C" fn lean_inc_heartbeat() {}

        #[no_mangle]
        pub unsafe extern "C" fn lean_get_num_heartbeats() -> u64 { 0 }

        #[no_mangle]
        pub unsafe extern "C" fn lean_set_heartbeats(_count: u64) {}

        pub unsafe fn initialize_alloc() {}
        pub unsafe fn finalize_alloc() {}
    }

    // -----------------------------------------------------------------------
    // Re-export initialize/finalize under the mangled C++ names used by
    // initialize/init.cpp.
    // -----------------------------------------------------------------------

    #[cfg(feature = "small_allocator")]
    #[export_name = "_ZN4lean16initialize_allocEv"]
    pub unsafe extern "C" fn initialize_alloc_export() {
        small_alloc::initialize_alloc();
    }

    #[cfg(not(feature = "small_allocator"))]
    #[export_name = "_ZN4lean16initialize_allocEv"]
    pub unsafe extern "C" fn initialize_alloc_export() {
        no_small_alloc::initialize_alloc();
    }

    #[cfg(feature = "small_allocator")]
    #[export_name = "_ZN4lean14finalize_allocEv"]
    pub unsafe extern "C" fn finalize_alloc_export() {
        small_alloc::finalize_alloc();
    }

    #[cfg(not(feature = "small_allocator"))]
    #[export_name = "_ZN4lean14finalize_allocEv"]
    pub unsafe extern "C" fn finalize_alloc_export() {
        no_small_alloc::finalize_alloc();
    }

    // -----------------------------------------------------------------------
    // C++ namespace helpers re-exported for use by the rest of the runtime
    // -----------------------------------------------------------------------

    #[cfg(feature = "small_allocator")]
    #[export_name = "_ZN4lean16init_thread_heapEv"]
    pub unsafe extern "C" fn init_thread_heap_export() {
        small_alloc::init_thread_heap();
    }

    #[cfg(feature = "small_allocator")]
    #[export_name = "_ZN4lean14set_heartbeatsEy"]
    pub unsafe extern "C" fn set_heartbeats_export(count: u64) {
        small_alloc::set_heartbeats(count);
    }

    #[cfg(feature = "small_allocator")]
    #[export_name = "_ZN4lean14add_heartbeatsEy"]
    pub unsafe extern "C" fn add_heartbeats_export(count: u64) {
        small_alloc::add_heartbeats(count);
    }

    #[cfg(feature = "small_allocator")]
    #[export_name = "_ZN4lean18get_num_heartbeatsEv"]
    pub unsafe extern "C" fn get_num_heartbeats_export() -> u64 {
        small_alloc::get_num_heartbeats()
    }

    // -----------------------------------------------------------------------
    // lean_sys_alloc / lean_sys_free_sized shims
    // -----------------------------------------------------------------------

    #[no_mangle]
    pub unsafe extern "C" fn lean_sys_alloc(sz: usize) -> *mut u8 {
        return libc::malloc(sz) as *mut u8;
    }

    #[no_mangle]
    pub unsafe extern "C" fn mi_malloc(sz: usize) -> *mut core::ffi::c_void {
        libc::malloc(sz)
    }

    #[no_mangle]
    pub unsafe extern "C" fn mi_malloc_small(sz: usize) -> *mut core::ffi::c_void {
        libc::malloc(sz)
    }

    #[no_mangle]
    pub unsafe extern "C" fn mi_free(ptr: *mut core::ffi::c_void) {
        libc::free(ptr);
    }

    #[no_mangle]
    pub unsafe extern "C" fn mi_free_size(ptr: *mut core::ffi::c_void, sz: usize) {
        let _ = sz;
        libc::free(ptr);
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_sys_free_sized(ptr: *mut u8, sz: usize) {
        let _ = sz;
        libc::free(ptr as *mut core::ffi::c_void);
        return;
    }
}
