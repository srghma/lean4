/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_thread_impl {
    use core::cell::Cell;
    use core::ffi::c_void;

    type ThreadFinalizer = unsafe extern "C" fn(*mut c_void);
    type FinalizerList = Vec<(ThreadFinalizer, *mut c_void)>;

    thread_local! {
        static G_FINALIZING: Cell<bool> = const { Cell::new(false) };
        static G_FINALIZERS: Cell<*mut FinalizerList> = const { Cell::new(core::ptr::null_mut()) };
        static G_POST_FINALIZERS: Cell<*mut FinalizerList> = const { Cell::new(core::ptr::null_mut()) };
    }

    unsafe fn register_finalizer(
        slot: &'static std::thread::LocalKey<Cell<*mut FinalizerList>>,
        f: ThreadFinalizer,
        data: *mut c_void,
    ) {
        slot.with(|cell| {
            let mut ptr = cell.get();
            if ptr.is_null() {
                ptr = Box::into_raw(Box::new(Vec::new()));
                cell.set(ptr);
            }
            unsafe {
                (*ptr).push((f, data));
            }
        });
    }

    unsafe fn run_finalizer_list(ptr: *mut FinalizerList) {
        if ptr.is_null() {
            return;
        }
        G_FINALIZING.with(|cell| cell.set(true));
        let list = &mut *ptr;
        let mut i = list.len();
        while i > 0 {
            i -= 1;
            let (f, data) = list[i];
            f(data);
        }
        list.clear();
        drop(Box::from_raw(ptr));
    }

    pub(crate) unsafe fn run_thread_finalizers_internal() {
        let ptr = G_FINALIZERS.with(|cell| {
            let ptr = cell.get();
            cell.set(core::ptr::null_mut());
            ptr
        });
        run_finalizer_list(ptr);
    }

    pub(crate) unsafe fn run_post_thread_finalizers_internal() {
        let ptr = G_POST_FINALIZERS.with(|cell| {
            let ptr = cell.get();
            cell.set(core::ptr::null_mut());
            ptr
        });
        run_finalizer_list(ptr);
    }

    pub(crate) unsafe fn delete_thread_finalizer_manager_internal() {
        let finalizers = G_FINALIZERS.with(|cell| {
            let ptr = cell.get();
            cell.set(core::ptr::null_mut());
            ptr
        });
        if !finalizers.is_null() {
            drop(Box::from_raw(finalizers));
        }
        let post_finalizers = G_POST_FINALIZERS.with(|cell| {
            let ptr = cell.get();
            cell.set(core::ptr::null_mut());
            ptr
        });
        if !post_finalizers.is_null() {
            drop(Box::from_raw(post_finalizers));
        }
    }

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_initialize_thread() {}

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_finalize_thread() {
        run_thread_finalizers_internal();
        run_post_thread_finalizers_internal();
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean22in_thread_finalizationEv")]
    pub extern "C" fn in_thread_finalization() -> bool {
        G_FINALIZING.with(|cell| cell.get())
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean25register_thread_finalizerEPFvPvES0_")]
    pub unsafe extern "C" fn register_thread_finalizer(f: ThreadFinalizer, data: *mut c_void) {
        register_finalizer(&G_FINALIZERS, f, data);
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean30register_post_thread_finalizerEPFvPvES0_")]
    pub unsafe extern "C" fn register_post_thread_finalizer(f: ThreadFinalizer, data: *mut c_void) {
        register_finalizer(&G_POST_FINALIZERS, f, data);
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean21run_thread_finalizersEv")]
    pub unsafe extern "C" fn run_thread_finalizers_export() {
        run_thread_finalizers_internal();
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean26run_post_thread_finalizersEv")]
    pub unsafe extern "C" fn run_post_thread_finalizers_export() {
        run_post_thread_finalizers_internal();
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean31delete_thread_finalizer_managerEv")]
    pub unsafe extern "C" fn delete_thread_finalizer_manager_export() {
        delete_thread_finalizer_manager_internal();
    }
}

pub(crate) use runtime_thread_impl::{
    delete_thread_finalizer_manager_internal, run_post_thread_finalizers_internal,
    run_thread_finalizers_internal,
};
