use std::mem;
use std::ptr;

#[repr(C)]
pub struct StackGuard {
    signal_stack: libc::stack_t,
}

unsafe fn install_signal_stack(signal_stack: *mut libc::stack_t) {
    (*signal_stack).ss_sp = libc::malloc(libc::SIGSTKSZ);
    if (*signal_stack).ss_sp.is_null() {
        return;
    }
    (*signal_stack).ss_size = libc::SIGSTKSZ;
    (*signal_stack).ss_flags = 0;
    libc::sigaltstack(signal_stack, ptr::null_mut());
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

pub unsafe fn stack_guard_ctor_complete(this: *mut StackGuard) {
    stack_guard_ctor(this);
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

unsafe fn stack_guard_dtor(this: *mut StackGuard) {
    uninstall_signal_stack(ptr::addr_of_mut!((*this).signal_stack));
}

pub unsafe fn stack_guard_dtor_complete(this: *mut StackGuard) {
    stack_guard_dtor(this);
}
