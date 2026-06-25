/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

#[cfg(all(feature = "std", unix))]
mod runtime_stack_overflow_impl {
    use super::*;
    use std::mem;
    use std::ptr;
    use std::sync::atomic::{AtomicPtr, Ordering};

    #[repr(C)]
    pub struct StackGuard {
        signal_stack: libc::stack_t,
    }

    static MAIN_STACK_GUARD: AtomicPtr<StackGuard> = AtomicPtr::new(ptr::null_mut());

    unsafe fn install_signal_stack(signal_stack: *mut libc::stack_t) {
        (*signal_stack).ss_sp = libc::malloc(libc::SIGSTKSZ);
        if (*signal_stack).ss_sp.is_null() {
            return;
        }
        (*signal_stack).ss_size = libc::SIGSTKSZ;
        (*signal_stack).ss_flags = 0;
        libc::sigaltstack(signal_stack, ptr::null_mut());
    }

    unsafe fn uninstall_signal_stack(signal_stack: *mut libc::stack_t) {
        if (*signal_stack).ss_sp.is_null() {
            return;
        }
        (*signal_stack).ss_flags = libc::SS_DISABLE;
        libc::sigaltstack(signal_stack, ptr::null_mut());
        libc::free((*signal_stack).ss_sp);
        (*signal_stack).ss_sp = ptr::null_mut();
    }

    unsafe fn stack_guard_ctor(this: *mut StackGuard) {
        ptr::write(
            this,
            StackGuard {
                signal_stack: mem::zeroed(),
            },
        );
        install_signal_stack(ptr::addr_of_mut!((*this).signal_stack));
    }

    unsafe fn stack_guard_dtor(this: *mut StackGuard) {
        uninstall_signal_stack(ptr::addr_of_mut!((*this).signal_stack));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardC1Ev"
    )]
    pub unsafe extern "C" fn stack_guard_ctor_complete(this: *mut StackGuard) {
        stack_guard_ctor(this);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardC2Ev"
    )]
    pub unsafe extern "C" fn stack_guard_ctor_base(this: *mut StackGuard) {
        stack_guard_ctor(this);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardD1Ev"
    )]
    pub unsafe extern "C" fn stack_guard_dtor_complete(this: *mut StackGuard) {
        stack_guard_dtor(this);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardD2Ev"
    )]
    pub unsafe extern "C" fn stack_guard_dtor_base(this: *mut StackGuard) {
        stack_guard_dtor(this);
    }

    #[cfg(target_os = "macos")]
    unsafe fn stack_low_address() -> Option<usize> {
        let self_thread = libc::pthread_self();
        let top = libc::pthread_get_stackaddr_np(self_thread) as usize;
        let size = libc::pthread_get_stacksize_np(self_thread);
        Some(top.wrapping_sub(size))
    }

    #[cfg(not(target_os = "macos"))]
    unsafe fn stack_low_address() -> Option<usize> {
        let mut attr: libc::pthread_attr_t = mem::zeroed();
        if libc::pthread_attr_init(&mut attr) != 0 {
            return None;
        }
        let mut stackaddr: *mut c_void = ptr::null_mut();
        let mut stacksize: usize = 0;
        let ok = libc::pthread_getattr_np(libc::pthread_self(), &mut attr) == 0
            && libc::pthread_attr_getstack(&attr, &mut stackaddr, &mut stacksize) == 0;
        libc::pthread_attr_destroy(&mut attr);
        if ok {
            Some(stackaddr as usize)
        } else {
            None
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean21is_within_stack_guardEPv"
    )]
    pub unsafe extern "C" fn is_within_stack_guard(addr: *mut c_void) -> bool {
        let Some(stackaddr) = stack_low_address() else {
            return false;
        };
        let guardsize = libc::sysconf(libc::_SC_PAGESIZE) as usize;
        let addr = addr as usize;
        stackaddr.wrapping_sub(guardsize) <= addr && addr < stackaddr
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn segv_handler(
        signum: c_int,
        info: *mut libc::siginfo_t,
        _: *mut c_void,
    ) {
        if !info.is_null() && is_within_stack_guard((*info).si_addr()) {
            let msg = b"\nStack overflow detected. Aborting.\n";
            libc::write(libc::STDERR_FILENO, msg.as_ptr().cast(), msg.len());
            libc::abort();
        } else {
            let mut action: libc::sigaction = mem::zeroed();
            action.sa_sigaction = libc::SIG_DFL;
            libc::sigaction(signum, &action, ptr::null_mut());
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean25initialize_stack_overflowEv"
    )]
    pub extern "C" fn initialize_stack_overflow() {
        unsafe {
            let guard = Box::into_raw(Box::new(StackGuard {
                signal_stack: mem::zeroed(),
            }));
            stack_guard_ctor(guard);
            MAIN_STACK_GUARD.store(guard, Ordering::Relaxed);
            for signum in [libc::SIGSEGV, libc::SIGBUS] {
                let mut action: libc::sigaction = mem::zeroed();
                libc::sigaction(signum, ptr::null(), &mut action);
                if action.sa_sigaction == libc::SIG_DFL {
                    action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
                    action.sa_sigaction = segv_handler as *const () as usize;
                    libc::sigemptyset(&mut action.sa_mask);
                    libc::sigaction(signum, &action, ptr::null_mut());
                }
            }
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean23finalize_stack_overflowEv"
    )]
    pub extern "C" fn finalize_stack_overflow() {
        let guard = MAIN_STACK_GUARD.swap(ptr::null_mut(), Ordering::Relaxed);
        if !guard.is_null() {
            unsafe {
                stack_guard_dtor(guard);
                drop(Box::from_raw(guard));
            }
        }
    }
}

#[cfg(all(feature = "std", unix))]
pub use runtime_stack_overflow_impl::*;

#[cfg(all(feature = "std", windows))]
mod runtime_stack_overflow_impl {
    use super::*;
    use std::process;

    #[repr(C)]
    pub struct StackGuard {
        _private: [u8; 0],
    }

    #[repr(C)]
    struct ExceptionRecord {
        exception_code: u32,
        exception_flags: u32,
        exception_record: *mut ExceptionRecord,
        exception_address: *mut c_void,
        number_parameters: usize,
        exception_information: [usize; 15],
    }

    #[repr(C)]
    struct ExceptionPointers {
        exception_record: *mut ExceptionRecord,
        context_record: *mut c_void,
    }

    extern "system" {
        fn SetThreadStackGuarantee(stack_size_in_bytes: *mut u32) -> i32;
        fn AddVectoredExceptionHandler(
            first: u32,
            handler: Option<unsafe extern "system" fn(*mut ExceptionPointers) -> i32>,
        ) -> *mut c_void;
    }

    const EXCEPTION_CONTINUE_SEARCH: i32 = 0;
    const EXCEPTION_STACK_OVERFLOW: u32 = 0xC00000FD;

    unsafe extern "system" fn stack_overflow_handler(info: *mut ExceptionPointers) -> i32 {
        if !info.is_null()
            && !(*info).exception_record.is_null()
            && (*(*info).exception_record).exception_code == EXCEPTION_STACK_OVERFLOW
        {
            eprintln!("\nStack overflow detected. Aborting.");
            process::abort();
        }
        EXCEPTION_CONTINUE_SEARCH
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardC1Ev"
    )]
    pub unsafe extern "C" fn stack_guard_ctor_complete(_: *mut StackGuard) {
        let mut size = 0x5000;
        SetThreadStackGuarantee(&mut size);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardC2Ev"
    )]
    pub unsafe extern "C" fn stack_guard_ctor_base(this: *mut StackGuard) {
        stack_guard_ctor_complete(this);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardD1Ev"
    )]
    pub unsafe extern "C" fn stack_guard_dtor_complete(_: *mut StackGuard) {}

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean11stack_guardD2Ev"
    )]
    pub unsafe extern "C" fn stack_guard_dtor_base(_: *mut StackGuard) {}

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean25initialize_stack_overflowEv"
    )]
    pub extern "C" fn initialize_stack_overflow() {
        unsafe {
            AddVectoredExceptionHandler(0, Some(stack_overflow_handler));
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean23finalize_stack_overflowEv"
    )]
    pub extern "C" fn finalize_stack_overflow() {}
}

#[cfg(all(feature = "std", windows))]
pub use runtime_stack_overflow_impl::*;
