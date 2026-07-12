use std::sync::atomic::Ordering;

pub static INITIALIZING: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(true);
pub fn lean_io_mark_end_initialization() {
    INITIALIZING.store(false, Ordering::Relaxed);
}
