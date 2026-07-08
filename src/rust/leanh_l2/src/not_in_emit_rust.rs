use core::ffi::c_void;
use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};
use libmimalloc_sys as mi;
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

use crate::datatypes::{
    LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_MPZ_TAG,
    LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG,
    LEAN_THUNK_TAG, LeanArrayObject, LeanClosureObject, LeanExternalObject, LeanMpzObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, ObjInitFn, Size,
};

use crate::in_emit_rust::{lean_is_scalar, lean_unbox};
use crate::runtime_object_panic::lean_internal_panic_out_of_memory;
use crate::runtime_object_rc::{lean_alloc_object, lean_mark_persistent};
use crate::runtime_object_task::{lean_runtime_deactivate_promise, lean_runtime_deactivate_task};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn get_next(o: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        let mut header: usize = 0;
        ptr::copy_nonoverlapping(o as *const u8, &mut header as *mut usize as *mut u8, 8);
        header &= !(0xffff_usize << 48);
        header as *mut LeanObject
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub fn lean_align(v: usize, a: usize) -> usize {
    (v / a) * a + a * (!v.is_multiple_of(a)) as usize
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanArrayObject<0>>()
            + core::mem::size_of::<*mut LeanObject>()
                * (*(obj as *const LeanArrayObject<0>)).m_capacity
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe { (*(obj as *mut LeanArrayObject<0>)).m_data.as_mut_ptr() }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    let array = obj as *const LeanArrayObject<0>;
    (*array).m_size
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_closure_set`, `lean_ctor_release`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_arg_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe { (*(obj as *mut LeanClosureObject<0>)).m_objs.as_mut_ptr() }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_closure_set`, `lean_ctor_release`, and 6 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_num_fixed(obj: *mut LeanObject) -> usize {
    unsafe { (*(obj as *const LeanClosureObject<0>)).m_num_fixed as usize }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanClosureObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * lean_closure_num_fixed(obj)
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, and 6 more EmitRust functions.
#[inline]
pub unsafe fn lean_global_alloc(size: usize) -> *mut u8 {
    unsafe {
        let layout = Layout::from_size_align(size.max(1), core::mem::align_of::<usize>()).unwrap();
        let mem = alloc(layout);
        if mem.is_null() {
            handle_alloc_error(layout);
        }
        mem
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_global_dealloc(mem: *mut u8, size: usize) {
    unsafe {
        let layout = Layout::from_size_align(size.max(1), core::mem::align_of::<usize>()).unwrap();
        dealloc(mem, layout);
    }
}

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
unsafe fn quar_free(o: *mut LeanObject) {
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

#[inline(always)]
pub unsafe fn lean_dealloc(o: *mut LeanObject, sz: usize) {
    unsafe {
        if UAF_DETECT {
            quar_free(o);
            return;
        }
        mi::mi_free_size(o as *mut c_void, sz);
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_free_small_object(o: *mut LeanObject) {
    if UAF_DETECT {
        unsafe { quar_free(o) };
        return;
    }
    unsafe { mi::mi_free_small(o as *mut c_void) };
}

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`, `lean_inc`, `lean_inc_n`, `lean_inc_ref`, and 2 more EmitRust functions.
#[inline]
pub unsafe fn lean_is_st(obj: *mut LeanObject) -> bool {
    unsafe { (*obj).rc > 0 }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
// #[inline]
// pub unsafe fn lean_mpz_clear(obj: *mut LeanObject) {
//     unsafe {
//         let mpz = &mut (*(obj as *mut LeanMpzObject)).m_value[0];
//         if !mpz.mp_d.is_null() {
//             libc::free(mpz.mp_d.cast());
//             mpz.mp_alloc = 0;
//             mpz.mp_size = 0;
//             mpz.mp_d = ptr::null_mut();
//         }
//     }
// }

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 28 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_num_objs(obj: *mut LeanObject) -> usize {
    unsafe {
        debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
        (*obj).other as usize
    }
}

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`.
#[inline]
pub unsafe fn lean_is_ref(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_REF_TAG }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_sarray_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanScalarArray<0>>()
            + (*obj).other as usize * (*(obj as *const LeanScalarArray<0>)).m_capacity
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_string_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanStringObject<0>>()
            + (*(obj as *const LeanStringObject<0>)).m_capacity
    }
}

// NOT IN EmitRust; here because it is used in `lean_mk_string`, `lean_mk_string_unchecked`.
#[inline]
pub unsafe fn lean_string_data(obj: *mut LeanObject) -> *mut u8 {
    unsafe {
        (*(obj as *mut LeanStringObject<0>))
            .m_data
            .as_mut_ptr()
            .cast::<u8>()
    }
}

// NOT IN EmitRust; here because it is used in `lean_obj_once`.
#[inline]
pub fn lock_once_cell(lock: &AtomicI32) {
    while lock
        .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        std::thread::yield_now();
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn pop_back(todo: &mut *mut LeanObject) -> *mut LeanObject {
    unsafe {
        let result = *todo;
        *todo = get_next(result);
        result
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn set_next(obj: *mut LeanObject, next: *mut LeanObject) {
    unsafe {
        let mut hi = 0u16;
        ptr::copy_nonoverlapping((obj as *const u8).add(6), &mut hi as *mut u16 as *mut u8, 2);
        let header = ((hi as usize) << 48) | (next as usize);
        ptr::copy_nonoverlapping(&header as *const usize as *const u8, obj as *mut u8, 8);
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn push_back(todo: &mut *mut LeanObject, obj: *mut LeanObject) {
    unsafe {
        set_next(obj, *todo);
        *todo = obj;
    }
}

// NOT IN EmitRust; here because it is used in `lean_obj_once`.
#[inline]
pub fn unlock_once_cell(lock: &AtomicI32) {
    lock.store(0, Ordering::Release);
}

// NOT IN EmitRust; here because it is used in `lean_float_once`, `lean_float32_once`, `lean_uint8_once`, `lean_uint16_once`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn run_once<T: Copy>(loc: *mut T, tok: *mut LeanOnceCell, init: unsafe fn() -> T) -> T {
    unsafe {
        let tok = &*tok;
        lock_once_cell(&tok.lock);
        if tok.state.load(Ordering::Acquire) != 1 {
            *loc = init();
            tok.state.store(1, Ordering::Release);
        }
        let result = *loc;
        unlock_once_cell(&tok.lock);
        result
    }
}

// NOT IN EmitRust; here because it is used in `lean_cstr_to_nat`, `lean_unsigned_to_nat`.
#[inline]
pub unsafe fn lean_usize_to_nat(value: usize) -> *mut LeanObject {
    unsafe {
        if value <= (usize::MAX >> 1) {
            lean_box(value)
        } else {
            panic!("big Nat is not supported in leanh.rs")
        }
    }
}

#[inline(always)]
pub unsafe fn lean_has_rc(o: *mut LeanObject) -> bool {
    unsafe { (*o).rc != 0 }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn dec_for_del(o: *mut LeanObject, todo: &mut *mut LeanObject) {
    unsafe {
        if lean_is_scalar_bool(o) {
            return;
        }
        if (*o).rc > 1 {
            (*o).rc -= 1;
        } else if (*o).rc == 1 {
            push_back(todo, o);
        } else if (*o).rc == 0 {
            return;
        } else if {
            let rc = core::ptr::addr_of_mut!((*o).rc).cast::<AtomicI32>();
            (*rc).fetch_add(1, Ordering::AcqRel) == -1
        } {
            push_back(todo, o);
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_del_core_other(o: *mut LeanObject, tag: u8, todo: &mut *mut LeanObject) {
    unsafe {
        match tag {
            LEAN_CLOSURE_TAG => {
                let it = lean_closure_arg_cptr(o);
                for i in 0..lean_closure_num_fixed(o) {
                    dec_for_del(*it.add(i), todo);
                }
                lean_dealloc(o, lean_closure_byte_size(o));
            }
            LEAN_ARRAY_TAG => {
                let it = lean_array_cptr(o);
                for i in 0..lean_array_size(o) {
                    dec_for_del(*it.add(i), todo);
                }
                lean_dealloc(o, lean_array_byte_size(o));
            }
            LEAN_SCALAR_ARRAY_TAG => {
                lean_dealloc(o, lean_sarray_byte_size(o));
            }
            LEAN_STRING_TAG => {
                lean_dealloc(o, lean_string_byte_size(o));
            }
            LEAN_MPZ_TAG => {
                let mpz = core::ptr::addr_of_mut!((*(o as *mut LeanMpzObject)).m_value);
                gmp_mpfr_sys::gmp::mpz_clear(mpz);
                lean_free_small_object(o);
            }
            LEAN_THUNK_TAG => {
                let t = o as *mut LeanThunkObject;
                let c = (*t).m_closure.load(Ordering::Acquire);
                if !c.is_null() {
                    dec_for_del(c, todo);
                }
                let v = (*t).m_value.load(Ordering::Acquire);
                if !v.is_null() {
                    dec_for_del(v, todo);
                }
                lean_free_small_object(o);
            }
            LEAN_REF_TAG => {
                let r = o as *mut LeanRefObject;
                if !(*r).m_value.is_null() {
                    dec_for_del((*r).m_value, todo);
                }
                lean_free_small_object(o);
            }
            LEAN_TASK_TAG => {
                lean_runtime_deactivate_task(o as *mut LeanTaskObject);
            }
            LEAN_PROMISE_TAG => {
                lean_runtime_deactivate_promise(o as *mut LeanPromiseObject);
            }
            LEAN_EXTERNAL_TAG => {
                let e = o as *mut LeanExternalObject;
                ((*(*e).m_class).m_finalize)((*e).m_data);
                lean_free_small_object(o);
            }
            _ => {
                crate::runtime_object_panic::lean_internal_panic(
                    c"lean_del_core: unknown object tag".as_ptr(),
                );
            }
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_del_core(obj: *mut LeanObject, todo: &mut *mut LeanObject) {
    unsafe {
        let tag = lean_ptr_tag(obj);
        if tag <= LEAN_MAX_CTOR_TAG {
            let fields = lean_ctor_obj_cptr(obj);
            for i in 0..lean_ctor_num_objs(obj) {
                dec_for_del(*fields.add(i), todo);
            }
            lean_free_small_object(obj);
        } else {
            lean_del_core_other(obj, tag, todo);
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_mk_string`, `lean_mk_string_unchecked`.
#[inline]
pub unsafe fn lean_alloc_string(byte_size: usize, capacity: usize, len: usize) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_object(core::mem::size_of::<LeanStringObject<0>>() + capacity)
            as *mut LeanStringObject<0>;
        (*obj).m_header.rc = 1;
        (*obj).m_header.cs_size = 0;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_STRING_TAG;
        (*obj).m_size = byte_size;
        (*obj).m_capacity = capacity;
        (*obj).m_length = len;
        obj as *mut LeanObject
    }
}

// NOT IN EmitRust; here because it is used in `lean_obj_once`.
#[inline]
pub unsafe fn lean_obj_once_cold(
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
    unsafe {
        let tok_ref = &*tok;
        lock_once_cell(&tok_ref.lock);
        if tok_ref.state.load(Ordering::Acquire) != 1 {
            *loc = init();
            lean_mark_persistent(*loc);
            tok_ref.state.store(1, Ordering::Release);
        }
        let result = *loc;
        unlock_once_cell(&tok_ref.lock);
        result
    }
}
