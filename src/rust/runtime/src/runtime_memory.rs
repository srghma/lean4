/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_memory_impl {
    use crate::*;
    use core::ffi::c_char;
    use std::cell::Cell;
    use std::sync::atomic::{AtomicUsize, Ordering};

    const LEAN_CHECK_MEM_THRESHOLD: usize = 200;

    static G_MAX_MEMORY: AtomicUsize = AtomicUsize::new(0);

    thread_local! {
        static G_COUNTER: Cell<usize> = Cell::new(0);
    }

    unsafe extern "C" {
        fn throw_memory_exception(component_name: *const c_char) -> !;
    }

    #[cfg(all(unix, not(target_os = "macos")))]
    unsafe fn get_peak_rss() -> usize {
        let mut rusage = std::mem::zeroed::<libc::rusage>();
        if libc::getrusage(libc::RUSAGE_SELF, &mut rusage) == 0 {
            (rusage.ru_maxrss as usize) * 1024
        } else {
            0
        }
    }

    #[cfg(target_os = "macos")]
    unsafe fn get_peak_rss() -> usize {
        let mut rusage = std::mem::zeroed::<libc::rusage>();
        if libc::getrusage(libc::RUSAGE_SELF, &mut rusage) == 0 {
            rusage.ru_maxrss as usize
        } else {
            0
        }
    }

    #[cfg(windows)]
    unsafe fn get_peak_rss() -> usize {
        use windows_sys::Win32::System::ProcessStatus::{
            GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS,
        };
        use windows_sys::Win32::System::Threading::GetCurrentProcess;
        let mut info = std::mem::zeroed::<PROCESS_MEMORY_COUNTERS>();
        info.cb = std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32;
        if GetProcessMemoryInfo(
            GetCurrentProcess(),
            &mut info,
            std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32,
        ) != 0
        {
            info.PeakWorkingSetSize as usize
        } else {
            0
        }
    }

    #[cfg(all(unix, not(target_os = "macos")))]
    unsafe fn get_current_rss() -> usize {
        if let Ok(content) = std::fs::read_to_string("/proc/self/statm") {
            let mut parts = content.split_whitespace();
            if parts.next().is_some() {
                if let Some(rss_str) = parts.next() {
                    if let Ok(rss) = rss_str.parse::<usize>() {
                        let page_size = libc::sysconf(libc::_SC_PAGESIZE) as usize;
                        return rss * page_size;
                    }
                }
            }
        }
        0
    }

    #[cfg(target_os = "macos")]
    unsafe fn get_current_rss() -> usize {
        use mach2::task_info::{
            MACH_TASK_BASIC_INFO, MACH_TASK_BASIC_INFO_COUNT, task_info, task_info_t,
        };
        use mach2::traps::mach_task_self;
        let mut info = std::mem::zeroed::<mach2::task_info::mach_task_basic_info>();
        let mut info_count = MACH_TASK_BASIC_INFO_COUNT;
        if task_info(
            mach_task_self(),
            MACH_TASK_BASIC_INFO,
            &mut info as *mut _ as task_info_t,
            &mut info_count,
        ) == 0
        {
            info.resident_size as usize
        } else {
            0
        }
    }

    #[cfg(windows)]
    unsafe fn get_current_rss() -> usize {
        use windows_sys::Win32::System::ProcessStatus::{
            GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS,
        };
        use windows_sys::Win32::System::Threading::GetCurrentProcess;
        let mut info = std::mem::zeroed::<PROCESS_MEMORY_COUNTERS>();
        info.cb = std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32;
        if GetProcessMemoryInfo(
            GetCurrentProcess(),
            &mut info,
            std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32,
        ) != 0
        {
            info.WorkingSetSize as usize
        } else {
            0
        }
    }

    pub fn lean_internal_get_default_max_memory() -> *mut LeanObject {
        const DEFAULT: usize = 0;

        unsafe { lean_box(DEFAULT) }
    }
    pub fn set_max_memory(max: usize) {
        G_MAX_MEMORY.store(max, Ordering::SeqCst);
    }

    pub fn lean_internal_set_max_memory(max: usize) -> *mut LeanObject {
        set_max_memory(max);
        unsafe { lean_box(0) }
    }
    pub fn set_max_memory_megabyte(max: u32) {
        let m = (max as usize).wrapping_mul(1024).wrapping_mul(1024);
        set_max_memory(m);
    }
    pub unsafe fn check_memory(component_name: *const c_char) {
        let max = G_MAX_MEMORY.load(Ordering::SeqCst);
        if max == 0 {
            return;
        }
        let counter = G_COUNTER.with(|cell| {
            let val = cell.get() + 1;
            cell.set(val);
            val
        });
        if counter >= LEAN_CHECK_MEM_THRESHOLD {
            G_COUNTER.with(|cell| cell.set(0));
            let r = get_peak_rss();
            if r > 0 && r < max {
                return;
            }
            let r = get_current_rss();
            if r == 0 || r < max {
                return;
            }
            throw_memory_exception(component_name);
        }
    }
    pub unsafe fn get_allocated_memory() -> usize {
        get_current_rss()
    }

    /// Returns `true` if memory usage is within configured limits.
    /// This is the Result-returning variant used by the Rust type checker.
    pub unsafe fn lean_memory_within_limit() -> bool {
        let max = G_MAX_MEMORY.load(Ordering::SeqCst);
        if max == 0 {
            return true;
        }
        let counter = G_COUNTER.with(|cell| {
            let val = cell.get() + 1;
            cell.set(val);
            val
        });
        if counter >= LEAN_CHECK_MEM_THRESHOLD {
            G_COUNTER.with(|cell| cell.set(0));
            let r = get_peak_rss();
            if r > 0 && r < max {
                return true;
            }
            let r = get_current_rss();
            if r == 0 || r < max {
                return true;
            }
            return false;
        }
        true
    }
}
pub use runtime_memory_impl::*;
