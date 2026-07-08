use leanh_l1::runtime_stack_overflow::p1::StackGuard;
use leanh_l1::runtime_stack_overflow::p1::stack_guard_ctor;
use std::ffi::c_int;
use std::ffi::c_void;
use std::mem;
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

static MAIN_STACK_GUARD: AtomicPtr<StackGuard> = AtomicPtr::new(ptr::null_mut());

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
    if ok { Some(stackaddr as usize) } else { None }
}
unsafe fn is_within_stack_guard(addr: *mut c_void) -> bool {
    let Some(stackaddr) = stack_low_address() else {
        return false;
    };
    let guardsize = libc::sysconf(libc::_SC_PAGESIZE) as usize;
    let addr = addr as usize;
    stackaddr.wrapping_sub(guardsize) <= addr && addr < stackaddr
}

unsafe fn segv_handler(signum: c_int, info: *mut libc::siginfo_t, _: *mut c_void) {
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

pub fn initialize_stack_overflow() {
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
