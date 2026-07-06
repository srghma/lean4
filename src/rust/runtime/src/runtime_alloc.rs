/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_alloc_impl {
    use std::cell::Cell;

    #[cfg(lean_small_allocator)]
    const LEAN_PAGE_SIZE: usize = 8192;
    #[cfg(lean_small_allocator)]
    const LEAN_SEGMENT_SIZE: usize = 8 * 1024 * 1024;
    #[cfg(lean_small_allocator)]
    const LEAN_OBJECT_SIZE_DELTA: usize = 8;
    #[cfg(lean_small_allocator)]
    const LEAN_MAX_SMALL_OBJECT_SIZE: usize = 4096;
    #[cfg(lean_small_allocator)]
    const LEAN_NUM_SLOTS: usize = LEAN_MAX_SMALL_OBJECT_SIZE / LEAN_OBJECT_SIZE_DELTA;
    #[cfg(lean_small_allocator)]
    const LEAN_MAX_TO_EXPORT_OBJS: usize = 1024;

    #[cfg(not(lean_small_allocator))]
    thread_local! {
        static G_HEARTBEAT: Cell<u64> = const { Cell::new(0) };
    }

    #[cfg(lean_small_allocator)]
    #[inline(always)]
    fn lean_align(size: usize, alignment: usize) -> usize {
        (size + alignment - 1) & !(alignment - 1)
    }

    #[cfg(lean_small_allocator)]
    #[inline(always)]
    fn lean_get_slot_idx(size: usize) -> usize {
        debug_assert!(size > 0);
        debug_assert_eq!(lean_align(size, LEAN_OBJECT_SIZE_DELTA), size);
        size / LEAN_OBJECT_SIZE_DELTA - 1
    }

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean16initialize_allocEv"
    )]
    pub extern "C" fn initialize_alloc() {}

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean14finalize_allocEv"
    )]
    pub extern "C" fn finalize_alloc() {}

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean14set_heartbeatsEm"
    )]
    pub unsafe fn set_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(count));
    }

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean14add_heartbeatsEm"
    )]
    pub unsafe fn add_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(cell.get().wrapping_add(count)));
    }

    #[cfg(not(lean_small_allocator))]
    pub unsafe fn lean_inc_heartbeat() {
        add_heartbeats(1);
    }

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean18get_num_heartbeatsEv"
    )]
    pub extern "C" fn get_num_heartbeats() -> u64 {
        G_HEARTBEAT.with(|cell| cell.get())
    }

    #[cfg(not(lean_small_allocator))]
    pub extern "C" fn lean_get_num_heartbeats() -> u64 {
        get_num_heartbeats()
    }

    #[cfg(not(lean_small_allocator))]
    pub extern "C" fn lean_set_heartbeats(count: u64) {
        unsafe {
            set_heartbeats(count);
        }
    }

    #[cfg(lean_small_allocator)]
    pub(crate) mod small {
        use super::*;
        use core::ffi::c_void;
        use core::sync::atomic::{AtomicPtr, Ordering};
        use std::sync::Mutex;

        extern "C" {
            fn lean_internal_panic_out_of_memory() -> !;
        }

        type ThreadFinalizer = unsafe fn(*mut c_void);

        #[repr(C)]
        struct PageHeader {
            heap: AtomicPtr<Heap>,
            next: *mut Page,
            prev: *mut Page,
            free_list: *mut u8,
            obj_size: u32,
            max_free: u32,
            num_free: u32,
            slot_idx: u32,
            in_page_free_list: bool,
        }

        #[repr(C)]
        struct Page {
            header: PageHeader,
        }

        impl Page {
            #[inline]
            unsafe fn data_start(this: *mut Page) -> *mut u8 {
                this.cast::<u8>().add(core::mem::size_of::<PageHeader>())
            }

            #[inline]
            fn has_many_free(&self) -> bool {
                self.header.num_free > self.header.max_free / 4
            }

            unsafe fn push_free_obj(this: *mut Page, obj: *mut u8) {
                debug_assert_eq!(get_page_of(obj), this);
                set_next_obj(obj, (*this).header.free_list);
                (*this).header.free_list = obj;
                (*this).header.num_free += 1;
                if !(*this).header.in_page_free_list && (*this).has_many_free() {
                    let heap = (*this).header.heap.load(Ordering::Relaxed);
                    let slot_idx = (*this).header.slot_idx as usize;
                    if this != (*heap).curr_page[slot_idx] {
                        (*this).header.in_page_free_list = true;
                        page_list_remove(&mut (*heap).curr_page[slot_idx], this);
                        page_list_insert(&mut (*heap).page_free_list[slot_idx], this);
                    }
                }
            }
        }

        #[repr(C)]
        struct Segment {
            next: *mut Segment,
            next_page_mem: *mut u8,
        }

        impl Segment {
            unsafe fn new() -> *mut Segment {
                let layout = std::alloc::Layout::from_size_align(
                    LEAN_SEGMENT_SIZE + LEAN_PAGE_SIZE,
                    LEAN_PAGE_SIZE,
                )
                .unwrap();
                let raw = std::alloc::alloc_zeroed(layout);
                if raw.is_null() {
                    lean_internal_panic_out_of_memory();
                }
                let segment = raw.cast::<Segment>();
                (*segment).next = core::ptr::null_mut();
                let first_page = lean_align(
                    raw.add(core::mem::size_of::<Segment>()) as usize,
                    LEAN_PAGE_SIZE,
                ) as *mut u8;
                (*segment).next_page_mem = first_page;
                segment
            }

            #[inline]
            unsafe fn is_full(segment: *mut Segment) -> bool {
                (*segment).next_page_mem.add(LEAN_PAGE_SIZE)
                    > segment.cast::<u8>().add(LEAN_SEGMENT_SIZE + LEAN_PAGE_SIZE)
            }
        }

        struct Heap {
            curr_segment: *mut Segment,
            next_orphan: *mut Heap,
            curr_page: [*mut Page; LEAN_NUM_SLOTS],
            page_free_list: [*mut Page; LEAN_NUM_SLOTS],
            to_export_list: *mut u8,
            to_export_list_size: usize,
            mutex: Mutex<*mut u8>,
            heartbeat: u64,
        }

        impl Heap {
            unsafe fn new() -> *mut Heap {
                Box::into_raw(Box::new(Heap {
                    curr_segment: core::ptr::null_mut(),
                    next_orphan: core::ptr::null_mut(),
                    curr_page: [core::ptr::null_mut(); LEAN_NUM_SLOTS],
                    page_free_list: [core::ptr::null_mut(); LEAN_NUM_SLOTS],
                    to_export_list: core::ptr::null_mut(),
                    to_export_list_size: 0,
                    mutex: Mutex::new(core::ptr::null_mut()),
                    heartbeat: 0,
                }))
            }

            unsafe fn import_objs(heap: *mut Heap) {
                let mut to_import = {
                    let mut guard = (*heap).mutex.lock().unwrap();
                    let list = *guard;
                    *guard = core::ptr::null_mut();
                    list
                };
                while !to_import.is_null() {
                    let page = get_page_of(to_import);
                    let next = get_next_obj(to_import);
                    Page::push_free_obj(page, to_import);
                    to_import = next;
                }
            }

            unsafe fn export_objs(heap: *mut Heap) {
                struct ExportEntry {
                    heap: *mut Heap,
                    head: *mut u8,
                    tail: *mut u8,
                }

                let mut to_export = Vec::<ExportEntry>::new();
                let mut obj = (*heap).to_export_list;
                while !obj.is_null() {
                    let next = get_next_obj(obj);
                    let target = (*get_page_of(obj)).header.heap.load(Ordering::Relaxed);
                    if let Some(entry) = to_export.iter_mut().find(|entry| entry.heap == target) {
                        set_next_obj(obj, entry.head);
                        entry.head = obj;
                    } else {
                        set_next_obj(obj, core::ptr::null_mut());
                        to_export.push(ExportEntry {
                            heap: target,
                            head: obj,
                            tail: obj,
                        });
                    }
                    obj = next;
                }
                (*heap).to_export_list = core::ptr::null_mut();
                (*heap).to_export_list_size = 0;

                for entry in to_export {
                    let mut guard = (*entry.heap).mutex.lock().unwrap();
                    set_next_obj(entry.tail, *guard);
                    *guard = entry.head;
                }
            }

            unsafe fn alloc_segment(heap: *mut Heap) {
                let segment = Segment::new();
                (*segment).next = (*heap).curr_segment;
                (*heap).curr_segment = segment;
            }
        }

        struct HeapManager {
            mutex: Mutex<*mut Heap>,
        }

        unsafe impl Send for HeapManager {}
        unsafe impl Sync for HeapManager {}

        impl HeapManager {
            const fn new() -> HeapManager {
                HeapManager {
                    mutex: Mutex::new(core::ptr::null_mut()),
                }
            }

            unsafe fn push_orphan(&self, heap: *mut Heap) {
                let mut guard = self.mutex.lock().unwrap();
                (*heap).next_orphan = *guard;
                *guard = heap;
            }

            unsafe fn pop_orphan(&self) -> *mut Heap {
                let mut guard = self.mutex.lock().unwrap();
                let heap = *guard;
                if !heap.is_null() {
                    *guard = (*heap).next_orphan;
                }
                heap
            }
        }

        static G_HEAP_MANAGER: HeapManager = HeapManager::new();

        thread_local! {
            static G_HEAP: Cell<*mut Heap> = const { Cell::new(core::ptr::null_mut()) };
        }

        #[inline(always)]
        unsafe fn get_heap() -> *mut Heap {
            G_HEAP.with(|cell| cell.get())
        }

        #[inline(always)]
        unsafe fn set_next_obj(obj: *mut u8, next: *mut u8) {
            obj.cast::<*mut u8>().write(next);
        }

        #[inline(always)]
        unsafe fn get_next_obj(obj: *mut u8) -> *mut u8 {
            obj.cast::<*mut u8>().read()
        }

        #[inline(always)]
        fn get_page_of(obj: *mut u8) -> *mut Page {
            ((obj as usize / LEAN_PAGE_SIZE) * LEAN_PAGE_SIZE) as *mut Page
        }

        unsafe fn page_list_insert(head: &mut *mut Page, new_head: *mut Page) {
            if !(*head).is_null() {
                (**head).header.prev = new_head;
            }
            (*new_head).header.next = *head;
            (*new_head).header.prev = core::ptr::null_mut();
            *head = new_head;
        }

        unsafe fn page_list_remove(head: &mut *mut Page, to_remove: *mut Page) {
            if *head == to_remove {
                *head = (*to_remove).header.next;
            }
            let prev = (*to_remove).header.prev;
            if !prev.is_null() {
                (*prev).header.next = (*to_remove).header.next;
            }
            let next = (*to_remove).header.next;
            if !next.is_null() {
                (*next).header.prev = prev;
            }
        }

        unsafe fn page_list_pop(head: &mut *mut Page) -> *mut Page {
            debug_assert!(!(*head).is_null());
            let result = *head;
            *head = (*result).header.next;
            result
        }

        unsafe fn alloc_page(heap: *mut Heap, obj_size: usize) -> *mut Page {
            debug_assert_eq!(lean_align(obj_size, LEAN_OBJECT_SIZE_DELTA), obj_size);
            let segment = (*heap).curr_segment;
            let page = (*segment).next_page_mem.cast::<Page>();
            (*segment).next_page_mem = (*segment).next_page_mem.add(LEAN_PAGE_SIZE);
            if Segment::is_full(segment) {
                Heap::alloc_segment(heap);
            }

            let slot_idx = lean_get_slot_idx(obj_size);
            (*page).header.heap = AtomicPtr::new(heap);
            (*page).header.next = core::ptr::null_mut();
            (*page).header.prev = core::ptr::null_mut();
            (*page).header.free_list = core::ptr::null_mut();
            (*page).header.obj_size = obj_size as u32;
            (*page).header.slot_idx = slot_idx as u32;
            (*page).header.in_page_free_list = false;
            page_list_insert(&mut (*heap).curr_page[slot_idx], page);

            let data_start = Page::data_start(page);
            let data_end = page.cast::<u8>().add(LEAN_PAGE_SIZE);
            let mut curr_free = data_start;
            set_next_obj(curr_free, core::ptr::null_mut());
            let mut next_free = curr_free.add(obj_size);
            let mut num_free = 1u32;
            while next_free.add(obj_size) <= data_end {
                debug_assert_eq!(get_page_of(curr_free), page);
                set_next_obj(next_free, curr_free);
                curr_free = next_free;
                next_free = next_free.add(obj_size);
                num_free += 1;
            }

            (*page).header.free_list = curr_free;
            (*page).header.max_free = num_free;
            (*page).header.num_free = num_free;
            page
        }

        unsafe fn finalize_heap(data: *mut c_void) {
            let heap = data.cast::<Heap>();
            Heap::export_objs(heap);
            Heap::import_objs(heap);
            G_HEAP_MANAGER.push_orphan(heap);
        }

        unsafe fn init_heap(main: bool) {
            debug_assert!(get_heap().is_null());
            let heap = {
                let orphan = G_HEAP_MANAGER.pop_orphan();
                if !orphan.is_null() {
                    orphan
                } else {
                    let heap = Heap::new();
                    Heap::alloc_segment(heap);
                    let mut obj_size = LEAN_OBJECT_SIZE_DELTA;
                    for slot in 0..LEAN_NUM_SLOTS {
                        if (*heap).curr_page[slot].is_null() {
                            alloc_page(heap, obj_size);
                        }
                        obj_size += LEAN_OBJECT_SIZE_DELTA;
                    }
                    heap
                }
            };
            G_HEAP.with(|cell| cell.set(heap));
            if !main {
                super::super::runtime_thread_impl::register_thread_finalizer(
                    finalize_heap as ThreadFinalizer,
                    heap.cast::<c_void>(),
                );
            }
        }

        #[cfg_attr(
            feature = "export-runtime-ffi",
            export_name = "_ZN4lean16init_thread_heapEv"
        )]
        pub unsafe fn init_thread_heap() {
            init_heap(false);
        }

        unsafe fn lean_alloc_small_cold(
            sz: usize,
            slot_idx: usize,
            mut page: *mut Page,
        ) -> *mut u8 {
            let heap = get_heap();
            if (*heap).page_free_list[slot_idx].is_null() {
                Heap::import_objs(heap);
                debug_assert_eq!((*heap).curr_page[slot_idx], page);
                if (*page).header.free_list.is_null() {
                    page = alloc_page(heap, sz);
                }
            } else {
                page = page_list_pop(&mut (*heap).page_free_list[slot_idx]);
                (*page).header.in_page_free_list = false;
                page_list_insert(&mut (*heap).curr_page[slot_idx], page);
            }
            let result = (*page).header.free_list;
            debug_assert!(!result.is_null());
            (*page).header.free_list = get_next_obj(result);
            (*page).header.num_free -= 1;
            debug_assert_eq!(get_page_of(result), page);
            result
        }

        pub unsafe fn lean_alloc_small(sz: u32, slot_idx: u32) -> *mut c_void {
            let heap = get_heap();
            debug_assert!(!heap.is_null());
            (*heap).heartbeat = (*heap).heartbeat.wrapping_add(1);
            let slot_idx = slot_idx as usize;
            let page = (*heap).curr_page[slot_idx];
            let result = (*page).header.free_list;
            if result.is_null() {
                return lean_alloc_small_cold(sz as usize, slot_idx, page).cast::<c_void>();
            }
            (*page).header.free_list = get_next_obj(result);
            (*page).header.num_free -= 1;
            debug_assert_eq!(get_page_of(result), page);
            result.cast::<c_void>()
        }

        unsafe fn alloc(sz: usize) -> *mut c_void {
            let sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
            if sz > LEAN_MAX_SMALL_OBJECT_SIZE {
                let result = libc::malloc(sz);
                if result.is_null() {
                    lean_internal_panic_out_of_memory();
                }
                return result;
            }
            debug_assert!(!get_heap().is_null());
            let slot_idx = lean_get_slot_idx(sz);
            lean_alloc_small(sz as u32, slot_idx as u32)
        }

        pub unsafe fn alloc_export(sz: usize) -> *mut c_void {
            alloc(sz)
        }

        unsafe fn dealloc_small_core_cold(obj: *mut u8) {
            let heap = get_heap();
            set_next_obj(obj, (*heap).to_export_list);
            (*heap).to_export_list = obj;
            (*heap).to_export_list_size += 1;
            if (*heap).to_export_list_size > LEAN_MAX_TO_EXPORT_OBJS {
                Heap::export_objs(heap);
            }
        }

        unsafe fn dealloc_small_core(obj: *mut u8) {
            let mut heap = get_heap();
            if heap.is_null() {
                init_heap(false);
                heap = get_heap();
            }
            debug_assert!(!heap.is_null());
            let page = get_page_of(obj);
            if (*page).header.heap.load(Ordering::Relaxed) == heap {
                Page::push_free_obj(page, obj);
            } else {
                dealloc_small_core_cold(obj);
            }
        }

        unsafe fn dealloc(obj: *mut c_void, sz: usize) {
            let sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
            if sz > LEAN_MAX_SMALL_OBJECT_SIZE {
                libc::free(obj);
                return;
            }
            dealloc_small_core(obj.cast::<u8>());
        }

        pub unsafe fn dealloc_export(obj: *mut c_void, sz: usize) {
            dealloc(obj, sz);
        }

        pub unsafe fn lean_free_small(obj: *mut c_void) {
            dealloc_small_core(obj.cast::<u8>());
        }

        pub unsafe fn lean_small_mem_size(obj: *mut c_void) -> u32 {
            let page = get_page_of(obj.cast::<u8>());
            (*page).header.obj_size
        }

        #[cfg_attr(
            feature = "export-runtime-ffi",
            export_name = "_ZN4lean16initialize_allocEv"
        )]
        pub unsafe fn initialize_alloc() {
            init_heap(true);
        }

        #[cfg_attr(
            feature = "export-runtime-ffi",
            export_name = "_ZN4lean14finalize_allocEv"
        )]
        pub extern "C" fn finalize_alloc() {}

        #[cfg_attr(
            feature = "export-runtime-ffi",
            export_name = "_ZN4lean14set_heartbeatsEm"
        )]
        pub unsafe fn set_heartbeats(count: u64) {
            let heap = get_heap();
            if !heap.is_null() {
                (*heap).heartbeat = count;
            }
        }

        #[cfg_attr(
            feature = "export-runtime-ffi",
            export_name = "_ZN4lean14add_heartbeatsEm"
        )]
        pub unsafe fn add_heartbeats(count: u64) {
            let heap = get_heap();
            if !heap.is_null() {
                (*heap).heartbeat = (*heap).heartbeat.wrapping_add(count);
            }
        }

        pub unsafe fn lean_inc_heartbeat() {
            add_heartbeats(1);
        }

        #[cfg_attr(
            feature = "export-runtime-ffi",
            export_name = "_ZN4lean18get_num_heartbeatsEv"
        )]
        pub unsafe fn get_num_heartbeats() -> u64 {
            let heap = get_heap();
            if heap.is_null() { 0 } else { (*heap).heartbeat }
        }

        pub unsafe fn lean_get_num_heartbeats() -> u64 {
            get_num_heartbeats()
        }

        pub unsafe fn lean_set_heartbeats(count: u64) {
            set_heartbeats(count);
        }
    }
}

#[cfg(lean_small_allocator)]
pub(crate) use runtime_alloc_impl::small::{lean_get_num_heartbeats, lean_set_heartbeats};
#[cfg(not(lean_small_allocator))]
pub(crate) use runtime_alloc_impl::{lean_get_num_heartbeats, lean_set_heartbeats};
