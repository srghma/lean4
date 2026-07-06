/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_thread_impl {
    use super::{LeanObject, lean_box};
    use core::cell::Cell;
    use core::ffi::c_void;

    type ThreadFinalizer = unsafe fn(*mut c_void);
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
    pub extern "C" fn lean_initialize_thread() {}

    #[cfg(not(lean_small_allocator))]
    pub unsafe fn lean_finalize_thread() {
        run_thread_finalizers_internal();
        run_post_thread_finalizers_internal();
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean22in_thread_finalizationEv"
    )]
    pub extern "C" fn in_thread_finalization() -> bool {
        G_FINALIZING.with(|cell| cell.get())
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean25register_thread_finalizerEPFvPvES0_"
    )]
    pub unsafe fn register_thread_finalizer(f: ThreadFinalizer, data: *mut c_void) {
        register_finalizer(&G_FINALIZERS, f, data);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean30register_post_thread_finalizerEPFvPvES0_"
    )]
    pub unsafe fn register_post_thread_finalizer(f: ThreadFinalizer, data: *mut c_void) {
        register_finalizer(&G_POST_FINALIZERS, f, data);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean21run_thread_finalizersEv"
    )]
    pub unsafe fn run_thread_finalizers_export() {
        run_thread_finalizers_internal();
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean26run_post_thread_finalizersEv"
    )]
    pub unsafe fn run_post_thread_finalizers_export() {
        run_post_thread_finalizers_internal();
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean31delete_thread_finalizer_managerEv"
    )]
    pub unsafe fn delete_thread_finalizer_manager_export() {
        delete_thread_finalizer_manager_internal();
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean17initialize_threadEv"
    )]
    pub extern "C" fn initialize_thread() {}

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15finalize_threadEv"
    )]
    pub extern "C" fn finalize_thread() {}

    // -------------------------------------------------------------------------
    // LThread / lean_run_main
    // -------------------------------------------------------------------------

    use core::ffi::{c_char, c_int};
    use core::mem::MaybeUninit;
    use core::sync::atomic::{AtomicUsize, Ordering};
    use libc::{
        pthread_attr_destroy, pthread_attr_init, pthread_attr_setstacksize, pthread_attr_t,
        pthread_create, pthread_detach, pthread_join, pthread_t,
    };

    extern "C" {
        fn get_max_heartbeat() -> usize;
        fn set_max_heartbeat(max: usize);

        // lean_initialize_thread on small-allocator builds comes from C++ thread.cpp;
        // on non-small-allocator it's the Rust no-op defined above.
        #[cfg(lean_small_allocator)]
        fn lean_initialize_thread();
        // lean_finalize_thread on small-allocator builds comes from C++ thread.cpp.
        #[cfg(lean_small_allocator)]
        fn lean_finalize_thread();
    }

    const LEAN_STACK_BUFFER_SPACE: usize = 128 * 1024;

    #[cfg(not(target_os = "emscripten"))]
    const LEAN_DEFAULT_THREAD_STACK_SIZE: usize = 1024 * 1024 * 1024; // 1 GB
    #[cfg(target_os = "emscripten")]
    const LEAN_DEFAULT_THREAD_STACK_SIZE: usize = 8 * 1024 * 1024; // 8 MB

    static G_THREAD_STACK_SIZE: AtomicUsize = AtomicUsize::new(LEAN_DEFAULT_THREAD_STACK_SIZE);

    fn get_thread_stack_size() -> usize {
        G_THREAD_STACK_SIZE.load(Ordering::Relaxed)
    }

    fn set_thread_stack_size_internal(sz: usize) {
        G_THREAD_STACK_SIZE.store(sz + LEAN_STACK_BUFFER_SPACE, Ordering::Relaxed);
    }

    pub unsafe fn lean_internal_set_thread_stack_size(sz: usize) -> *mut LeanObject {
        set_thread_stack_size_internal(sz);
        lean_box(0)
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean7lthread21get_thread_stack_sizeEv"
    )]
    pub extern "C" fn lthread_get_thread_stack_size() -> usize {
        get_thread_stack_size()
    }

    type ThreadClosure = Box<dyn FnOnce() + Send + 'static>;

    extern "C" fn lthread_entry(p: *mut c_void) -> *mut c_void {
        unsafe {
            // Install per-thread alternate signal stack (same as C++ `stack_guard guard`)
            #[cfg(any(unix, windows))]
            let mut _guard = MaybeUninit::<super::StackGuard>::uninit();
            #[cfg(any(unix, windows))]
            super::stack_guard_ctor_complete(_guard.as_mut_ptr());

            lean_initialize_thread();
            let f = Box::from_raw(p as *mut ThreadClosure);
            (*f)();
            lean_finalize_thread();

            #[cfg(any(unix, windows))]
            super::stack_guard_dtor_complete(_guard.as_mut_ptr());
        }
        core::ptr::null_mut()
    }

    pub struct LThread {
        attr: pthread_attr_t,
        thread: pthread_t,
        joined: bool,
    }

    impl LThread {
        pub fn new(f: ThreadClosure) -> Self {
            unsafe {
                let stack_size = get_thread_stack_size();
                let mut attr = MaybeUninit::<pthread_attr_t>::uninit();
                if pthread_attr_init(attr.as_mut_ptr()) != 0 {
                    panic!("lean: failed to initialize thread attributes");
                }
                let mut attr = attr.assume_init();
                if pthread_attr_setstacksize(&mut attr, stack_size) != 0 {
                    pthread_attr_destroy(&mut attr);
                    panic!("lean: failed to set thread stack size");
                }
                let boxed: Box<ThreadClosure> = Box::new(f);
                let raw = Box::into_raw(boxed) as *mut c_void;
                let mut thread = MaybeUninit::<pthread_t>::uninit();
                if pthread_create(thread.as_mut_ptr(), &attr, lthread_entry, raw) != 0 {
                    drop(Box::from_raw(raw as *mut ThreadClosure));
                    pthread_attr_destroy(&mut attr);
                    panic!("lean: failed to create thread");
                }
                LThread {
                    attr,
                    thread: thread.assume_init(),
                    joined: false,
                }
            }
        }

        pub fn join(&mut self) {
            self.joined = true;
            unsafe {
                if pthread_join(self.thread, core::ptr::null_mut()) != 0 {
                    panic!("lean: failed to join thread");
                }
            }
        }
    }

    impl Drop for LThread {
        fn drop(&mut self) {
            unsafe {
                pthread_attr_destroy(&mut self.attr);
                if !self.joined {
                    pthread_detach(self.thread);
                }
            }
        }
    }

    type MainFn = unsafe fn(argc: c_int, argv: *mut *mut c_char) -> *mut LeanObject;

    struct SendPtr<T>(*mut T);
    unsafe impl<T> Send for SendPtr<T> {}
    impl<T> SendPtr<T> {
        fn get(self) -> *mut T {
            self.0
        }
    }

    #[cfg(lean_multi_thread)]
    pub unsafe fn lean_run_main(
        main_fn: MainFn,
        argc: c_int,
        argv: *mut *mut c_char,
    ) -> *mut LeanObject {
        if let Ok(val) = std::env::var("LEAN_STACK_SIZE_KB") {
            if let Ok(kb) = val.trim().parse::<u64>() {
                let sz = (kb / 4 * 4 * 1024) as usize;
                if sz > 0 {
                    set_thread_stack_size_internal(sz);
                }
            }
        }
        if let Ok(val) = std::env::var("LEAN_MAIN_USE_THREAD") {
            if val.trim() == "0" {
                return main_fn(argc, argv);
            }
        }
        let max_hb = get_max_heartbeat();
        let mut result: *mut LeanObject = core::ptr::null_mut();
        let result_ptr = SendPtr(&mut result as *mut *mut LeanObject);
        let argv_send = SendPtr(argv);
        let mut t = LThread::new(Box::new(move || unsafe {
            set_max_heartbeat(max_hb);
            let r = main_fn(argc, argv_send.get());
            *result_ptr.get() = r;
        }));
        t.join();
        result
    }

    #[cfg(not(lean_multi_thread))]
    pub unsafe fn lean_run_main(
        main_fn: MainFn,
        argc: c_int,
        argv: *mut *mut c_char,
    ) -> *mut LeanObject {
        main_fn(argc, argv)
    }

    // The C++ thread-local reset registry is currently unused in the tree.
    // Keep the hooks as no-ops so we can retire src/runtime/thread.cpp.
    pub unsafe fn register_thread_local_reset_fn(_fn: *mut c_void) {}

    pub unsafe fn reset_thread_local() {}
}

pub(crate) use runtime_thread_impl::{
    delete_thread_finalizer_manager_internal, run_post_thread_finalizers_internal,
    run_thread_finalizers_internal,
};
