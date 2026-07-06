use core::cell::Cell;
use core::ffi::c_void;
use core::sync::atomic::{AtomicUsize, Ordering};

type ThreadFinalizer = unsafe fn(*mut c_void);
type FinalizerList = Vec<(ThreadFinalizer, *mut c_void)>;

thread_local! {
    static G_FINALIZING: Cell<bool> = const { Cell::new(false) };
    static G_FINALIZERS: Cell<*mut FinalizerList> = const { Cell::new(core::ptr::null_mut()) };
    static G_POST_FINALIZERS: Cell<*mut FinalizerList> = const { Cell::new(core::ptr::null_mut()) };
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

pub unsafe fn run_thread_finalizers_internal() {
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

const LEAN_DEFAULT_THREAD_STACK_SIZE: usize = 1024 * 1024 * 1024; // 1 GB

static G_THREAD_STACK_SIZE: AtomicUsize = AtomicUsize::new(LEAN_DEFAULT_THREAD_STACK_SIZE);

fn get_thread_stack_size() -> usize {
    G_THREAD_STACK_SIZE.load(Ordering::Relaxed)
}

pub fn lthread_get_thread_stack_size() -> usize {
    get_thread_stack_size()
}

pub fn lean_initialize_thread() {}

pub unsafe fn lean_finalize_thread() {
    run_thread_finalizers_internal();
    run_post_thread_finalizers_internal();
}
