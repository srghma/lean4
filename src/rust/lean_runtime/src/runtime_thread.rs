// Port of src/runtime/thread.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.

mod runtime_thread_impl {
    use super::*;
    use core::cell::Cell;
    use core::ffi::c_void;
    use core::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Mutex, OnceLock};


    // ---------------------------------------------------------------------------
    // Thread-local reset functions
    // These are registered once at startup and called before each task/command
    // to invalidate stale caches.
    // ---------------------------------------------------------------------------

    static G_THREAD_LOCAL_RESET_FNS: OnceLock<Mutex<Vec<unsafe extern "C" fn()>>> =
        OnceLock::new();

    fn reset_fns() -> &'static Mutex<Vec<unsafe extern "C" fn()>> {
        G_THREAD_LOCAL_RESET_FNS.get_or_init(|| Mutex::new(Vec::new()))
    }

    /// Register a C-callable function that resets a thread-local cache.
    /// Must only be called during initialization (single-threaded startup).
    #[no_mangle]
    pub unsafe extern "C" fn lean_register_thread_local_reset_fn(f: unsafe extern "C" fn()) {
        reset_fns().lock().unwrap().push(f);
    }

    /// Reset all registered thread-local caches.
    /// Called before processing each command and before executing each task.
    #[no_mangle]
    pub unsafe extern "C" fn lean_reset_thread_local() {
        let fns = reset_fns().lock().unwrap();
        for f in fns.iter() {
            f();
        }
    }

    // ---------------------------------------------------------------------------
    // Stack size
    // ---------------------------------------------------------------------------

    #[cfg(target_os = "emscripten")]
    const LEAN_DEFAULT_THREAD_STACK_SIZE: usize = 8 * 1024 * 1024; // 8 MB (32-bit)

    #[cfg(not(target_os = "emscripten"))]
    const LEAN_DEFAULT_THREAD_STACK_SIZE: usize = 1024 * 1024 * 1024; // 1 GB (64-bit)

    const LEAN_STACK_BUFFER_SPACE: usize = 128 * 1024; // 128 KB

    static G_THREAD_STACK_SIZE: AtomicUsize =
        AtomicUsize::new(LEAN_DEFAULT_THREAD_STACK_SIZE);

    fn get_thread_stack_size() -> usize {
        G_THREAD_STACK_SIZE.load(Ordering::Relaxed)
    }

    fn set_thread_stack_size(sz: usize) {
        G_THREAD_STACK_SIZE.store(sz + LEAN_STACK_BUFFER_SPACE, Ordering::Relaxed);
    }

    /// `setThreadStackSize (sz : USize) : BaseIO Unit`
    #[no_mangle]
    pub unsafe extern "C" fn lean_internal_set_thread_stack_size(sz: usize) -> *mut LeanObject {
        set_thread_stack_size(sz);
        lean_box(0)
    }

    // ---------------------------------------------------------------------------
    // Thread initializer/finalizer (called for every worker thread)
    // ---------------------------------------------------------------------------

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
        G_FINALIZING.with(|cell| cell.set(false));
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

    extern "C" {
        fn lean_initialize_thread_heap();
    }

    #[no_mangle]
    pub unsafe extern "C" fn register_thread_finalizer(f: ThreadFinalizer, data: *mut c_void) {
        register_finalizer(&G_FINALIZERS, f, data);
    }

    #[no_mangle]
    pub unsafe extern "C" fn register_post_thread_finalizer(f: ThreadFinalizer, data: *mut c_void) {
        register_finalizer(&G_POST_FINALIZERS, f, data);
    }

    #[no_mangle]
    pub extern "C" fn in_thread_finalization() -> bool {
        G_FINALIZING.with(|cell| cell.get())
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_initialize_thread() {
        #[cfg(feature = "small_allocator")]
        lean_initialize_thread_heap();
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_finalize_thread() {
        run_thread_finalizers_internal();
        run_post_thread_finalizers_internal();
    }

    // ---------------------------------------------------------------------------
    // lthread — a thread with a configurable stack size
    //
    // On Linux/macOS we use pthreads via libc.
    // On Windows we use CreateThread.
    // The single-thread (no-multi-thread) build just runs the closure inline.
    // ---------------------------------------------------------------------------

    // The thread entry trampoline: initializes the thread heap, runs the
    // closure, then finalizes.
    unsafe fn thread_main(f: Box<dyn FnOnce() + Send + 'static>) {
        lean_initialize_thread();
        f();
        lean_finalize_thread();
    }

    // ---- pthreads implementation (Linux / macOS) --------------------------------
    #[cfg(all(not(windows), not(target_os = "emscripten")))]
    mod lthread_impl {
        use super::*;
        use libc::{
            pthread_attr_destroy, pthread_attr_init, pthread_attr_setstacksize, pthread_attr_t,
            pthread_create, pthread_detach, pthread_join, pthread_t,
        };
        use std::mem::MaybeUninit;

        extern "C" fn thread_entry(p: *mut c_void) -> *mut c_void {
            unsafe {
                let mut guard = MaybeUninit::<StackGuard>::uninit();
                stack_guard_ctor_complete(guard.as_mut_ptr());
                // Reconstruct the Box from the raw pointer and run it.
                let f = Box::from_raw(p as *mut Box<dyn FnOnce() + Send + 'static>);
                thread_main(*f);
                stack_guard_dtor_complete(guard.as_mut_ptr());
            }
            std::ptr::null_mut()
        }

        pub struct LThread {
            attr: pthread_attr_t,
            thread: pthread_t,
            joined: bool,
        }

        impl LThread {
            pub fn new(f: Box<dyn FnOnce() + Send + 'static>) -> Self {
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

                    // Double-box so we can pass a thin *mut c_void.
                    let boxed: Box<Box<dyn FnOnce() + Send + 'static>> = Box::new(f);
                    let raw = Box::into_raw(boxed) as *mut c_void;

                    let mut thread = MaybeUninit::<pthread_t>::uninit();
                    if pthread_create(thread.as_mut_ptr(), &attr, thread_entry, raw) != 0 {
                        // Reclaim the box to avoid leaking.
                        drop(Box::from_raw(raw as *mut Box<dyn FnOnce() + Send + 'static>));
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
                    if pthread_join(self.thread, std::ptr::null_mut()) != 0 {
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
    }

    // ---- Windows implementation -------------------------------------------------
    #[cfg(windows)]
    mod lthread_impl {
        use super::*;
        use windows_sys::Win32::System::Threading::{
            CloseHandle, CreateThread, WaitForSingleObject, INFINITE,
            STACK_SIZE_PARAM_IS_A_RESERVATION,
        };

        unsafe extern "system" fn thread_entry(p: *mut c_void) -> u32 {
            let f = Box::from_raw(p as *mut Box<dyn FnOnce() + Send + 'static>);
            thread_main(*f);
            0
        }

        pub struct LThread {
            handle: isize, // HANDLE
        }

        impl LThread {
            pub fn new(f: Box<dyn FnOnce() + Send + 'static>) -> Self {
                unsafe {
                    let stack_size = get_thread_stack_size();
                    let boxed: Box<Box<dyn FnOnce() + Send + 'static>> = Box::new(f);
                    let raw = Box::into_raw(boxed) as *mut c_void;

                    let handle = CreateThread(
                        std::ptr::null(),
                        stack_size,
                        Some(thread_entry),
                        raw,
                        STACK_SIZE_PARAM_IS_A_RESERVATION,
                        std::ptr::null_mut(),
                    );
                    if handle == 0 {
                        drop(Box::from_raw(raw as *mut Box<dyn FnOnce() + Send + 'static>));
                        panic!("lean: failed to create thread");
                    }
                    LThread { handle }
                }
            }

            pub fn join(&mut self) {
                unsafe {
                    if WaitForSingleObject(self.handle, INFINITE) != 0 {
                        panic!("lean: failed to join thread");
                    }
                }
            }
        }

        impl Drop for LThread {
            fn drop(&mut self) {
                unsafe {
                    CloseHandle(self.handle);
                }
            }
        }
    }

    // ---- Single-thread stub (emscripten / no-multi-thread) ----------------------
    #[cfg(target_os = "emscripten")]
    mod lthread_impl {
        use super::*;

        pub struct LThread;

        impl LThread {
            pub fn new(f: Box<dyn FnOnce() + Send + 'static>) -> Self {
                // Run inline on the calling thread.
                unsafe { thread_main(f) };
                LThread
            }
            pub fn join(&mut self) {}
        }
    }

    use lthread_impl::LThread;

    // ---------------------------------------------------------------------------
    // lean_run_main
    //
    // Reads LEAN_STACK_SIZE_KB / LEAN_MAIN_USE_THREAD env vars, then either
    // calls main_fn directly or spawns an lthread with the configured stack.
    // ---------------------------------------------------------------------------

    type MainFn = unsafe extern "C" fn(argc: i32, argv: *mut *mut i8) -> *mut LeanObject;

    #[no_mangle]
    pub unsafe extern "C" fn lean_run_main(
        main_fn: MainFn,
        argc: i32,
        argv: *mut *mut i8,
    ) -> *mut LeanObject {
        // Check LEAN_STACK_SIZE_KB
        if let Ok(val) = std::env::var("LEAN_STACK_SIZE_KB") {
            if let Ok(kb) = val.trim().parse::<u64>() {
                let sz = (kb / 4 * 4 * 1024) as usize; // align to 4KB, convert to bytes
                if sz > 0 {
                    set_thread_stack_size(sz);
                }
            }
        }

        // Check LEAN_MAIN_USE_THREAD=0 to skip thread spawning.
        if let Ok(val) = std::env::var("LEAN_MAIN_USE_THREAD") {
            if val.trim() == "0" {
                return main_fn(argc, argv);
            }
        }

        // Spawn a new thread with the configured stack size and run main there.
        let mut result: *mut LeanObject = std::ptr::null_mut();
        {
            // We need to pass argc/argv into the closure. They are valid for
            // the duration of the process so the raw pointer send is safe here.
            let result_ptr = SendPtr(&mut result as *mut *mut LeanObject);
            let argv_send = SendPtr(argv as *mut *mut u8);
            let mut t = LThread::new(Box::new(move || {
                let r = main_fn(argc, argv_send.get() as *mut *mut i8);
                unsafe { *result_ptr.get() = r };
            }));
            t.join();
        }
        result
    }

    // ---------------------------------------------------------------------------
    // Module initializer / finalizer pair (NOT for individual threads).
    // Called once from the Lean process initializer.
    // ---------------------------------------------------------------------------

    /// Initialize the thread subsystem (module init, not per-thread init).
    #[export_name = "_ZN4lean17initialize_threadEv"]
    pub unsafe extern "C" fn initialize_thread_module() {
        // The reset-fn list is lazily initialized via OnceLock, so nothing
        // explicit is needed here. This function exists to mirror the C++
        // initialize_thread() / finalize_thread() module init pair.
    }

    /// Finalize the thread subsystem (module init, not per-thread finalize).
    #[export_name = "_ZN4lean15finalize_threadEv"]
    pub unsafe extern "C" fn finalize_thread_module() {
        // Nothing to do: the OnceLock<Mutex<Vec>> leaks intentionally
        // (same as the C++ `delete g_thread_local_reset_fns`).
    }
}

pub(crate) use runtime_thread_impl::{
    delete_thread_finalizer_manager_internal, run_post_thread_finalizers_internal,
    run_thread_finalizers_internal,
};
