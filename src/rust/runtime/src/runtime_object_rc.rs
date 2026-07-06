/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the RC / deallocation / object graph traversal section of
// src/runtime/object.cpp.

pub(crate) mod runtime_object_rc_impl {
    use crate::*;
    use core::ffi::c_void;
    use core::ptr;
    use core::sync::atomic::{AtomicI32, Ordering};
    use leanh::{
        LeanArrayObject, LeanClosureObject, LeanExternalClass, LeanExternalObject, LeanMpzObject,
        LeanObject, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
        LeanTaskObject, LeanThunkObject, LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG,
        LEAN_MAX_CTOR_TAG, LEAN_MPZ_TAG, LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG,
        LEAN_STRING_TAG, LEAN_TASK_TAG, LEAN_THUNK_TAG, MpzT,
    };
    use libmimalloc_sys as mi;
    #[cfg(all(lean_has_address_sanitizer, unix))]
    use libloading::os::unix::Library as UnixLibrary;

    const LEAN_MAX_SMALL_OBJECT_SIZE: usize = 4096;

    #[cfg(all(lean_has_address_sanitizer, unix))]
    unsafe fn ignore_lsan_object(ptr: *mut c_void) {
        let lib = UnixLibrary::this();
        if let Ok(ignore) = unsafe { lib.get::<unsafe fn(*mut c_void)>(c"__lsan_ignore_object") } {
            unsafe { (*ignore)(ptr) };
        }
    }

    #[cfg(not(all(lean_has_address_sanitizer, unix)))]
    unsafe fn ignore_lsan_object(_: *mut c_void) {}

    unsafe extern "C" {
        fn lean_internal_panic(msg: *const i8) -> !;
        fn lean_internal_panic_out_of_memory() -> !;
        fn lean_task_get(task: *mut LeanObject) -> *mut LeanObject;
        fn lean_runtime_deactivate_task(task: *mut LeanTaskObject);
        fn lean_runtime_deactivate_promise(promise: *mut LeanPromiseObject);
    }

    #[inline(always)]
    unsafe fn lean_is_st(o: *mut LeanObject) -> bool { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 141 (🔁)
        (*o).rc > 0
    }

    #[inline(always)]
    unsafe fn lean_has_rc(o: *mut LeanObject) -> bool {
        (*o).rc != 0
    }

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
        mi::mi_free(p as *mut c_void);
    }
    #[cold]
    pub(crate) unsafe fn quar_report_uaf(o: *mut LeanObject, op: &str) {
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
    unsafe fn quar_free(o: *mut LeanObject) {
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

    #[inline(always)]
    unsafe fn lean_dealloc(o: *mut LeanObject, sz: usize) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 125 (🔁)
        if UAF_DETECT {
            quar_free(o);
            return;
        }
        mi::mi_free_size(o as *mut c_void, sz);
    }

    #[inline(always)]
    unsafe fn lean_array_cptr(o: *mut LeanObject) -> *mut *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 46 (🔁)
        (*(o as *mut LeanArrayObject<0>)).m_data.as_mut_ptr()
    }

    #[inline(always)]
    unsafe fn lean_array_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 52 (🔁)
        (*(o as *const LeanArrayObject<0>)).m_size
    }

    #[inline(always)]
    unsafe fn lean_array_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 36 (🔁)
        core::mem::size_of::<LeanArrayObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * (*(o as *const LeanArrayObject<0>)).m_capacity
    }

    #[inline(always)]
    unsafe fn lean_sarray_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 197 (🔁)
        core::mem::size_of::<LeanScalarArray<0>>()
            + (*o).other as usize * (*(o as *const LeanScalarArray<0>)).m_capacity
    }

    #[inline(always)]
    unsafe fn lean_string_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 206 (🔁)
        core::mem::size_of::<LeanStringObject<0>>() + (*(o as *const LeanStringObject<0>)).m_capacity
    }

    #[inline(always)]
    unsafe fn lean_closure_arg_cptr(o: *mut LeanObject) -> *mut *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 58 (🔁)
        (*(o as *mut LeanClosureObject<0>)).m_objs.as_mut_ptr()
    }

    #[inline(always)]
    unsafe fn lean_closure_num_fixed(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 64 (🔁)
        (*(o as *const LeanClosureObject<0>)).m_num_fixed as usize
    }

    #[inline(always)]
    unsafe fn lean_closure_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 70 (🔁)
        core::mem::size_of::<LeanClosureObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * lean_closure_num_fixed(o)
    }

    #[inline(always)]
    unsafe fn lean_ctor_num_objs(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 167 (🔁)
        (*o).other as usize
    }

    #[inline(always)]
    unsafe fn lean_ctor_obj_cptr(o: *mut LeanObject) -> *mut *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 176 (🔁)
        (o as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut *mut LeanObject
    }

    #[inline(always)]
    unsafe fn lean_alloc_closure(fun: *mut c_void, arity: u32, num_fixed: u32) -> *mut LeanObject { // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 264 (🔁)
        debug_assert!(arity > 0);
        debug_assert!(num_fixed < arity);
        let byte_size = core::mem::size_of::<LeanClosureObject<0>>()
            .checked_add(
                core::mem::size_of::<*mut LeanObject>()
                    .checked_mul(num_fixed as usize)
                    .expect("closure allocation overflow"),
            )
            .expect("closure allocation overflow");
        let obj = lean_alloc_object(byte_size) as *mut LeanClosureObject<0>;
        (*obj).m_header.rc = 1;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_CLOSURE_TAG;
        (*obj).m_fun = fun;
        (*obj).m_arity = arity as u16;
        (*obj).m_num_fixed = num_fixed as u16;
        (*obj).m_header.cs_size = 0;
        obj as *mut LeanObject
    }

    #[inline(always)]
    pub(crate) unsafe fn lean_alloc_small_object(sz: usize) -> *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 92 (🔁)
        let sz = ((sz + 7) / 8) * 8;
        let mem = mi::mi_malloc_small(sz);
        if mem.is_null() {
            lean_internal_panic_out_of_memory();
        }
        let o = mem as *mut LeanObject;
        (*o).cs_size = sz as u16;
        o
    }

    #[inline(always)]
    pub(crate) unsafe fn lean_free_small_object(o: *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 133 (🔁)
        if UAF_DETECT {
            quar_free(o);
            return;
        }
        mi::mi_free_small(o as *mut c_void);
    }

    #[inline(always)]
    pub(crate) unsafe fn lean_alloc_ctor_memory(sz: usize) -> *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 103 (🔁)
        let sz1 = ((sz + 7) / 8) * 8;
        let r = lean_alloc_small_object(sz1);
        if sz1 > sz {
            let end = (r as *mut u8).add(sz1) as *mut usize;
            end.sub(1).write(0);
        }
        r
    }

    #[inline(always)]
    unsafe fn get_next(o: *mut LeanObject) -> *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 16 (🔁)
        let mut header: usize = 0;
        ptr::copy_nonoverlapping(o as *const u8, &mut header as *mut usize as *mut u8, 8);
        header &= !(0xffff_usize << 48);
        header as *mut LeanObject
    }

    #[inline(always)]
    unsafe fn set_next(o: *mut LeanObject, next: *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 265 (🔁)
        let mut hi: u16 = 0;
        ptr::copy_nonoverlapping((o as *const u8).add(6), &mut hi as *mut u16 as *mut u8, 2);
        let header: usize = ((hi as usize) << 48) | (next as usize);
        ptr::copy_nonoverlapping(&header as *const usize as *const u8, o as *mut u8, 8);
    }

    #[inline(always)]
    unsafe fn push_back(todo: &mut *mut LeanObject, v: *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 279 (🔁)
        set_next(v, *todo);
        *todo = v;
    }

    #[inline(always)]
    unsafe fn pop_back(todo: &mut *mut LeanObject) -> *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 255 (🔁)
        let r = *todo;
        *todo = get_next(r);
        r
    }

    #[inline(always)]
    unsafe fn dec_for_del(o: *mut LeanObject, todo: &mut *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 353 (🔁)
        if lean_is_scalar(o) {
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

    #[inline(always)]
    unsafe fn lean_del_core_other(o: *mut LeanObject, tag: u8, todo: &mut *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 373 (🔁)
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
                let mpz = &mut (*(o as *mut LeanMpzObject)).m_value as *mut MpzT;
                __gmpz_clear(mpz);
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
                lean_internal_panic(c"lean_del_core: unknown object tag".as_ptr());
            }
        }
    }

    #[inline(always)]
    unsafe fn lean_del_core(o: *mut LeanObject, todo: &mut *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 442 (🔁)
        let tag = lean_ptr_tag(o);
        if tag <= LEAN_MAX_CTOR_TAG {
            let it = lean_ctor_obj_cptr(o);
            for i in 0..lean_ctor_num_objs(o) {
                dec_for_del(*it.add(i), todo);
            }
            lean_free_small_object(o);
        } else {
            lean_del_core_other(o, tag, todo);
        }
    }

    pub unsafe fn lean_alloc_object(sz: usize) -> *mut LeanObject { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 459 (🔁)
        let r = mi::mi_malloc(sz);
        if r.is_null() {
            lean_internal_panic_out_of_memory();
        }
        let o = r as *mut LeanObject;
        (*o).cs_size = 0;
        o
    }

    pub unsafe fn lean_alloc_ctor_memory_export(sz: usize) -> *mut LeanObject {
        lean_alloc_ctor_memory(sz)
    }

    pub unsafe fn lean_free_object(o: *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 215 (🔁)
        match lean_ptr_tag(o) {
            LEAN_ARRAY_TAG => lean_dealloc(o, lean_array_byte_size(o)),
            LEAN_SCALAR_ARRAY_TAG => lean_dealloc(o, lean_sarray_byte_size(o)),
            LEAN_STRING_TAG => lean_dealloc(o, lean_string_byte_size(o)),
            LEAN_CLOSURE_TAG => lean_dealloc(o, lean_closure_byte_size(o)),
            LEAN_MPZ_TAG => {
                let mpz = &mut (*(o as *mut LeanMpzObject)).m_value as *mut MpzT;
                __gmpz_clear(mpz);
                lean_free_small_object(o);
            }
            _ => lean_free_small_object(o),
        }
    }

    pub unsafe fn lean_dec_ref_cold(mut o: *mut LeanObject) { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 486 (🔁)
        if lean_is_scalar(o) {
            return;
        }
        if (*o).rc == 1 || {
            let rc = core::ptr::addr_of_mut!((*o).rc).cast::<AtomicI32>();
            (*rc).fetch_add(1, Ordering::AcqRel) == -1
        } {
            let mut todo = ptr::null_mut();
            loop {
                lean_del_core(o, &mut todo);
                if todo.is_null() {
                    return;
                }
                o = pop_back(&mut todo);
            }
        }
    }

    #[cfg(lean_has_address_sanitizer)]
    #[inline(always)]
    unsafe fn lsan_ignore(o: *mut LeanObject) {
        ignore_lsan_object(o as *mut c_void);
    }

    #[cfg(not(lean_has_address_sanitizer))]
    #[inline(always)]
    unsafe fn lsan_ignore(_o: *mut LeanObject) {}

    pub unsafe fn lean_mark_persistent(o: *mut LeanObject) { // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 356 (🔁)
        let mut todo = vec![o];
        while let Some(cur) = todo.pop() {
            if !lean_is_scalar(cur) && lean_has_rc(cur) {
                (*cur).rc = 0;
                lsan_ignore(cur);
                let tag = lean_ptr_tag(cur);
                if tag <= LEAN_MAX_CTOR_TAG {
                    let it = lean_ctor_obj_cptr(cur);
                    for i in 0..lean_ctor_num_objs(cur) {
                        todo.push(*it.add(i));
                    }
                } else {
                    match tag {
                        LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG | LEAN_MPZ_TAG => {}
                        LEAN_EXTERNAL_TAG => {
                            let fn_obj =
                                lean_alloc_closure(mark_persistent_fn as *mut c_void, 1, 0);
                            let e = cur as *mut LeanExternalObject;
                            ((*(*e).m_class).m_foreach)((*e).m_data, fn_obj);
                            lean_dec(fn_obj);
                        }
                        LEAN_TASK_TAG => {
                            todo.push(lean_task_get(cur));
                        }
                        LEAN_PROMISE_TAG => {
                            let p = cur as *mut LeanPromiseObject;
                            todo.push((*p).m_result as *mut LeanObject);
                        }
                        LEAN_CLOSURE_TAG => {
                            let it = lean_closure_arg_cptr(cur);
                            for i in 0..lean_closure_num_fixed(cur) {
                                todo.push(*it.add(i));
                            }
                        }
                        LEAN_ARRAY_TAG => {
                            let it = lean_array_cptr(cur);
                            for i in 0..lean_array_size(cur) {
                                todo.push(*it.add(i));
                            }
                        }
                        LEAN_THUNK_TAG => {
                            let t = cur as *mut LeanThunkObject;
                            let c = (*t).m_closure.load(Ordering::Acquire);
                            if !c.is_null() {
                                todo.push(c);
                            }
                            let v = (*t).m_value.load(Ordering::Acquire);
                            if !v.is_null() {
                                todo.push(v);
                            }
                        }
                        LEAN_REF_TAG => {
                            let r = cur as *mut LeanRefObject;
                            if !(*r).m_value.is_null() {
                                todo.push((*r).m_value);
                            }
                        }
                        _ => {
                            lean_internal_panic(c"lean_mark_persistent: unknown tag".as_ptr());
                        }
                    }
                }
            }
        }
    }

    unsafe fn mark_persistent_fn(o: *mut LeanObject) -> *mut LeanObject {
        lean_mark_persistent(o);
        lean_box(0)
    }

    #[cfg(not(lean_multi_thread))]
    pub unsafe fn lean_mark_mt(_o: *mut LeanObject) {}

    #[cfg(lean_multi_thread)]
    pub unsafe fn lean_mark_mt(o: *mut LeanObject) {
        if lean_is_scalar(o) || !lean_is_st(o) {
            return;
        }

        let mut todo = vec![o];
        while let Some(cur) = todo.pop() {
            if !lean_is_scalar(cur) && lean_is_st(cur) {
                (*cur).rc = -(*cur).rc;
                let tag = lean_ptr_tag(cur);
                if tag <= LEAN_MAX_CTOR_TAG {
                    let it = lean_ctor_obj_cptr(cur);
                    for i in 0..lean_ctor_num_objs(cur) {
                        todo.push(*it.add(i));
                    }
                } else {
                    match tag {
                        LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG | LEAN_MPZ_TAG => {}
                        LEAN_EXTERNAL_TAG => {
                            let fn_obj = lean_alloc_closure(mark_mt_fn as *mut c_void, 1, 0);
                            let e = cur as *mut LeanExternalObject;
                            ((*(*e).m_class).m_foreach)((*e).m_data, fn_obj);
                            lean_dec(fn_obj);
                        }
                        LEAN_TASK_TAG => {
                            todo.push(lean_task_get(cur));
                        }
                        LEAN_PROMISE_TAG => {
                            let p = cur as *mut LeanPromiseObject;
                            todo.push((*p).m_result as *mut LeanObject);
                        }
                        LEAN_CLOSURE_TAG => {
                            let it = lean_closure_arg_cptr(cur);
                            for i in 0..lean_closure_num_fixed(cur) {
                                todo.push(*it.add(i));
                            }
                        }
                        LEAN_ARRAY_TAG => {
                            let it = lean_array_cptr(cur);
                            for i in 0..lean_array_size(cur) {
                                todo.push(*it.add(i));
                            }
                        }
                        LEAN_THUNK_TAG => {
                            let t = cur as *mut LeanThunkObject;
                            let c = (*t).m_closure.load(Ordering::Acquire);
                            if !c.is_null() {
                                todo.push(c);
                            }
                            let v = (*t).m_value.load(Ordering::Acquire);
                            if !v.is_null() {
                                todo.push(v);
                            }
                        }
                        LEAN_REF_TAG => {
                            let r = cur as *mut LeanRefObject;
                            if !(*r).m_value.is_null() {
                                todo.push((*r).m_value);
                            }
                        }
                        _ => {
                            lean_internal_panic(c"lean_mark_mt: unknown tag".as_ptr());
                        }
                    }
                }
            }
        }
    }

    unsafe fn mark_mt_fn(o: *mut LeanObject) -> *mut LeanObject {
        lean_mark_mt(o);
        lean_dec(o);
        lean_box(0)
    }
}
