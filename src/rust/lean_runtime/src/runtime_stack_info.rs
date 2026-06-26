/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

pub(crate) mod runtime_stack_info_impl {
    use super::*;
    use core::ffi::c_char;
    use std::cell::Cell;

    const LEAN_STACK_BUFFER_SPACE: usize = 128 * 1024; // 128 Kb

    extern "C" {
        #[link_name = "_ZN4lean7lthread21get_thread_stack_sizeEv"]
        fn lthread_get_thread_stack_size() -> usize;
    }

    thread_local! {
        static G_STACK_INFO_INIT: Cell<bool> = Cell::new(false);
        static G_STACK_SIZE: Cell<usize> = Cell::new(0);
        static G_STACK_BASE: Cell<usize> = Cell::new(0);
        static G_STACK_THRESHOLD: Cell<usize> = Cell::new(0);
    }

    #[inline(always)]
    fn get_stack_pointer() -> usize {
        let dummy = 0u8;
        &dummy as *const u8 as usize
    }

    #[cfg(all(unix, not(target_os = "emscripten")))]
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

    #[cfg(target_os = "emscripten")]
    extern "C" {
        fn emscripten_stack_get_end() -> usize;
        fn emscripten_stack_get_base() -> usize;
    }

    #[cfg(target_os = "emscripten")]
    unsafe fn get_stack_size(main: bool) -> usize {
        if main {
            emscripten_stack_get_end().saturating_sub(emscripten_stack_get_base())
        } else {
            lthread_get_thread_stack_size()
        }
    }

    #[cfg(windows)]
    unsafe fn get_stack_size(main: bool) -> usize {
        if main {
            const LEAN_WIN_STACK_SIZE: usize = 104857600;
            LEAN_WIN_STACK_SIZE
        } else {
            lthread_get_thread_stack_size()
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean14get_stack_sizeEb"
    )]
    pub unsafe extern "C" fn get_stack_size_export(main: bool) -> usize {
        get_stack_size(main)
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15save_stack_infoEb"
    )]
    pub unsafe extern "C" fn save_stack_info_export(main: bool) {
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

    #[inline]
    pub(crate) unsafe fn save_stack_info(main: bool) {
        save_stack_info_export(main);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean19get_used_stack_sizeEv"
    )]
    pub unsafe extern "C" fn get_used_stack_size_export() -> usize {
        let curr = get_stack_pointer();
        let base = G_STACK_BASE.with(|cell| cell.get());
        base.saturating_sub(curr)
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean24get_available_stack_sizeEv"
    )]
    pub unsafe extern "C" fn get_available_stack_size_export() -> usize {
        let used = get_used_stack_size_export();
        let size = G_STACK_SIZE.with(|cell| cell.get());
        size.saturating_sub(used)
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11check_stackEPKc"
    )]
    pub unsafe extern "C" fn check_stack_export(component_name: *const c_char) {
        let init = G_STACK_INFO_INIT.with(|cell| cell.get());
        if !init {
            save_stack_info_export(false);
        }
        let curr = get_stack_pointer();
        let threshold = G_STACK_THRESHOLD.with(|cell| cell.get());
        if curr < threshold {
            throw_stack_space_exception(component_name);
        }
    }

    /// Returns `true` if there is enough stack space (no deep recursion detected).
    /// This is the Result-returning variant used by the Rust type checker.
    pub unsafe fn lean_stack_has_space() -> bool {
        let init = G_STACK_INFO_INIT.with(|cell| cell.get());
        if !init {
            save_stack_info_export(false);
        }
        let curr = get_stack_pointer();
        let threshold = G_STACK_THRESHOLD.with(|cell| cell.get());
        curr >= threshold
    }
}
pub(crate) use runtime_stack_info_impl::*;
