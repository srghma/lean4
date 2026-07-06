use crate::runtime_thread::lthread_get_thread_stack_size;
use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
use std::cell::Cell;

#[cfg(unix)]

thread_local! {
    static G_STACK_INFO_INIT: Cell<bool> = Cell::new(false);
    static G_STACK_SIZE: Cell<usize> = Cell::new(0);
    static G_STACK_BASE: Cell<usize> = Cell::new(0);
    static G_STACK_THRESHOLD: Cell<usize> = Cell::new(0);
}

unsafe fn get_stack_size(main: bool) -> usize {
    if main {
        let mut limit = std::mem::zeroed::<libc::rlimit>();
        if libc::getrlimit(libc::RLIMIT_STACK, &mut limit) != 0 {
            use crate::runtime_exception::throw_get_stack_size_failed;

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

const LEAN_STACK_BUFFER_SPACE: usize = 128 * 1024; // 128 Kb
pub unsafe fn save_stack_info_export(main: bool) {
    let size = get_stack_size(main);
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

pub unsafe fn save_stack_info(main: bool) {
    save_stack_info_export(main);
}
