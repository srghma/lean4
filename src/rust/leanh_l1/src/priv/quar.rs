use libmimalloc_sys as mi;
use std::{ffi::c_void, ptr, sync::atomic::Ordering};

use crate::{datatypes::LeanObject, r#priv::lean_ptr_tag::lean_ptr_tag};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
// ===================== over-free / use-after-free detector (DEBUG) =====================
// Poison `(*o).rc = i32::MIN` at the PHYSICAL-free choke points and park the block in a
// bounded quarantine; a later inc/dec of a parked block (checked in lib.rs) is a UAF. The
// free-site backtrace is captured into a large ring so the report names the over-decrement.
pub(crate) const UAF_DETECT: bool = false;
pub(crate) const LEAN_UAF_POISON_RC: i32 = i32::MIN;
const QSET_SIZE: usize = 1 << 21;
const QSET_MASK: usize = QSET_SIZE - 1;
const QRING_SIZE: usize = 1 << 18;
static QSET: [core::sync::atomic::AtomicUsize; QSET_SIZE] =
    [const { core::sync::atomic::AtomicUsize::new(0) }; QSET_SIZE];
static QRING: [core::sync::atomic::AtomicUsize; QRING_SIZE] =
    [const { core::sync::atomic::AtomicUsize::new(0) }; QRING_SIZE];
static QHEAD: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
const FB_N: usize = 1 << 19;
const FB_D: usize = 24;
static mut FB_PTR: [usize; FB_N] = [0; FB_N];
static mut FB_BT: [[*mut c_void; FB_D]; FB_N] = [[ptr::null_mut(); FB_D]; FB_N];
static FB_HEAD: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
#[inline(always)]
fn qhash(p: usize) -> usize {
    (p >> 4) & QSET_MASK
}
#[inline(always)]
unsafe fn quar_phys_free(p: usize) {
    unsafe {
        mi::mi_free(p as *mut c_void);
    }
}
#[cold]
pub(crate) unsafe fn quar_report_uaf(o: *mut LeanObject, op: &str) {
    unsafe {
        eprintln!(
            "\n=== USE-AFTER-FREE DETECTED ({} of a freed/quarantined object) ===",
            op
        );
        eprintln!("obj={:p} tag={} other={}", o, lean_ptr_tag(o), (*o).other);
        let w = o as *const u64;
        eprintln!(
            "words: [0]={:#018x} [1]={:#018x} [2]={:#018x} [3]={:#018x}",
            *w,
            *w.add(1),
            *w.add(2),
            *w.add(3)
        );
        let p = o as usize;
        for i in 0..FB_N {
            if *core::ptr::addr_of!(FB_PTR[i]) == p {
                eprintln!(">>> FREE-SITE (over-decrement) backtrace:");
                libc::backtrace_symbols_fd(
                    core::ptr::addr_of!(FB_BT[i]) as *const *mut c_void,
                    FB_D as i32,
                    2,
                );
                break;
            }
        }
        eprintln!("--- current backtrace ---");
        let mut bt = [ptr::null_mut::<c_void>(); 32];
        let n = libc::backtrace(bt.as_mut_ptr(), 32);
        libc::backtrace_symbols_fd(bt.as_ptr(), n, 2);
        std::process::abort();
    }
}
#[used]
static KEEP_QUAR_REPORT_UAF: unsafe fn(*mut LeanObject, &str) = quar_report_uaf;
pub unsafe fn quar_free(o: *mut LeanObject) {
    unsafe {
        let p = o as usize;
        let i = FB_HEAD.fetch_add(1, Ordering::Relaxed) % FB_N;
        let row = core::ptr::addr_of_mut!(FB_BT[i]) as *mut *mut c_void;
        for k in 0..FB_D {
            *row.add(k) = ptr::null_mut();
        }
        libc::backtrace(row, FB_D as i32);
        *core::ptr::addr_of_mut!(FB_PTR[i]) = p;
        let h = qhash(p);
        QSET[h].store(p, Ordering::Relaxed);
        (*o).rc = LEAN_UAF_POISON_RC;
        let idx = QHEAD.fetch_add(1, Ordering::Relaxed) & (QRING_SIZE - 1);
        let old = QRING[idx].swap(p, Ordering::Relaxed);
        if old != 0 {
            let oh = qhash(old);
            let _ = QSET[oh].compare_exchange(old, 0, Ordering::Relaxed, Ordering::Relaxed);
            quar_phys_free(old);
        }
    }
}
