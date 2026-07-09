use std::cell::Cell;

use crate::{
    runtime_exception::throw_get_stack_size_failed,
    runtime_thread::{p2::lthread_get_thread_stack_size, p3::LEAN_STACK_BUFFER_SPACE},
};

#[cfg(unix)]

thread_local! {
    static G_STACK_INFO_INIT: Cell<bool> = const { Cell::new(false) };
    static G_STACK_SIZE: Cell<usize> = const { Cell::new(0) };
    static G_STACK_BASE: Cell<usize> = const { Cell::new(0) };
    static G_STACK_THRESHOLD: Cell<usize> = const { Cell::new(0) };
}
unsafe fn get_stack_size(main: bool) -> usize {
    if main {
        let mut limit = std::mem::zeroed::<libc::rlimit>();
        if libc::getrlimit(libc::RLIMIT_STACK, &mut limit) != 0 {
            throw_get_stack_size_failed();
        }
        limit.rlim_cur as usize
    } else {
        lthread_get_thread_stack_size()
    }
}

#[inline(always)]
fn get_stack_pointer() -> usize {
    let dummy = 0u8;
    &dummy as *const u8 as usize
}

pub fn save_stack_info(main: bool) {
    let size = unsafe { get_stack_size(main) };
    let base = get_stack_pointer();

    let mut threshold = base
        .wrapping_add(LEAN_STACK_BUFFER_SPACE)
        .wrapping_sub(size);
    if threshold > base.wrapping_add(LEAN_STACK_BUFFER_SPACE) {
        threshold = 0;
    }

    G_STACK_INFO_INIT.with(|cell| cell.set(true));
    G_STACK_SIZE.with(|cell| cell.set(size));
    G_STACK_BASE.with(|cell| cell.set(base));
    G_STACK_THRESHOLD.with(|cell| cell.set(threshold));
}
