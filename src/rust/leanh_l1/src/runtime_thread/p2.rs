use core::sync::atomic::{AtomicUsize, Ordering};
const LEAN_DEFAULT_THREAD_STACK_SIZE: usize = 1024 * 1024 * 1024; // 1 GB

static G_THREAD_STACK_SIZE: AtomicUsize = AtomicUsize::new(LEAN_DEFAULT_THREAD_STACK_SIZE);

pub fn lthread_get_thread_stack_size() -> usize {
    G_THREAD_STACK_SIZE.load(Ordering::Relaxed)
}
