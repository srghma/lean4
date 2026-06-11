/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the RC slow-path / object graph traversal section of src/runtime/object.cpp.
// Coverage:
//   get_next / set_next  (pointer-packing worklist)
//   lean_free_object
//   lean_dec_ref_cold
//   lean_del_core  (destructor trampoline, inline deletion loop)
//   lean_mark_persistent
//   lean_mark_mt
//   lean_alloc_ctor_memory_export
//   lean_object_byte_size / lean_free_object dealloc helpers



// ─── External C++ helpers we still depend on ─────────────────────────────────

extern "C" {
    // Sized-free: C23 / glibc extension, falls back to plain free() in C++.
    fn free_sized(ptr: *mut c_void, sz: usize);

    // Free a "small" object (i.e. one allocated with lean_alloc_small_object /
    // lean_alloc_ctor).  Defined in lean.h as an inline.
    fn lean_free_small_object(o: *mut LeanObject);

    // MPZ destructor shim — calls `to_mpz(o)->m_value.~mpz()` then
    // lean_free_small_object.  Must be provided by the C++ side.
    fn lean_runtime_free_mpz_object(o: *mut LeanObject);

    // Thunk / Ref field accessors (lean.h inlines).
    fn lean_to_thunk(o: *mut LeanObject) -> *mut LeanThunkObject;
    fn lean_to_ref(o: *mut LeanObject) -> *mut LeanRefObject;
    fn lean_to_external(o: *mut LeanObject) -> *mut LeanExternalObject;
    fn lean_to_promise(o: *mut LeanObject) -> *mut LeanPromiseObject;

    // Constructor field accessors.
    fn lean_ctor_obj_cptr(o: *mut LeanObject) -> *mut *mut LeanObject;
    fn lean_ctor_num_objs(o: *mut LeanObject) -> c_uint;

    // Closure field accessors.
    fn lean_closure_arg_cptr(o: *mut LeanObject) -> *mut *mut LeanObject;
    fn lean_closure_num_fixed(o: *mut LeanObject) -> c_uint;

    // Array field accessors.
    fn lean_array_cptr(o: *mut LeanObject) -> *mut *mut LeanObject;

    // Alloc helpers.
    fn lean_alloc_ctor_memory(sz: usize) -> *mut LeanObject;
}

// ─── Lean object-tag constants (must match lean.h) ───────────────────────────

const LEAN_MAX_CTOR_TAG: u8 = 244;
const LEAN_ARRAY_TAG: u8 = 246;
const LEAN_SCALAR_ARRAY_TAG: u8 = 248;
const LEAN_STRING_TAG: u8 = 249;
const LEAN_CLOSURE_TAG: u8 = 250;
const LEAN_MPZ_TAG: u8 = 251;
const LEAN_THUNK_TAG: u8 = 252;
const LEAN_TASK_TAG: u8 = 253;
const LEAN_REF_TAG: u8 = 254;
const LEAN_EXTERNAL_TAG: u8 = 245;
const LEAN_PROMISE_TAG: u8 = 247;

// ─── Deallocation helper ─────────────────────────────────────────────────────

#[inline(always)]
unsafe fn lean_dealloc(o: *mut LeanObject, sz: usize) {
    free_sized(o as *mut c_void, sz);
}

// ─── Pointer-packed intrusive worklist ───────────────────────────────────────
//
// The C++ code re-uses the first 6 bytes of an object's header to store the
// next pointer in a singly-linked worklist.  On 64-bit hosts the top 2 bytes
// of the header word are preserved so the object tag survives; on 32-bit the
// first pointer slot is simply overwritten.
//
// Invariant: objects in the worklist have RC == 1 (i.e. we own them) so it is
// safe to scribble over the header temporarily.

#[cfg(target_pointer_width = "64")]
unsafe fn get_next(o: *mut LeanObject) -> *mut LeanObject {
    // Read the full 8-byte header word.
    let mut header: usize = 0;
    core::ptr::copy_nonoverlapping(o as *const u8, &mut header as *mut usize as *mut u8, 8);
    // Zero the top 2 bytes (tag + other fields stored there) so the value is
    // a clean 48-bit pointer.
    header &= !(0xffff_usize << 48);
    header as *mut LeanObject
}

#[cfg(target_pointer_width = "64")]
unsafe fn set_next(o: *mut LeanObject, next: *mut LeanObject) {
    // Preserve the top 2 bytes of the header (tag byte lives at offset 7).
    let mut hi: u16 = 0;
    core::ptr::copy_nonoverlapping(
        (o as *const u8).add(6),
        &mut hi as *mut u16 as *mut u8,
        2,
    );
    let header: usize = ((hi as usize) << 48) | (next as usize);
    core::ptr::copy_nonoverlapping(&header as *const usize as *const u8, o as *mut u8, 8);
}

#[cfg(target_pointer_width = "32")]
unsafe fn get_next(o: *mut LeanObject) -> *mut LeanObject {
    *(o as *mut *mut LeanObject)
}

#[cfg(target_pointer_width = "32")]
unsafe fn set_next(o: *mut LeanObject, next: *mut LeanObject) {
    *(o as *mut *mut LeanObject) = next;
}

#[inline(always)]
unsafe fn push_back(todo: &mut *mut LeanObject, v: *mut LeanObject) {
    set_next(v, *todo);
    *todo = v;
}

#[inline(always)]
unsafe fn pop_back(todo: &mut *mut LeanObject) -> *mut LeanObject {
    let r = *todo;
    *todo = get_next(r);
    r
}

// ─── Dec helper used inside the deletion loop ─────────────────────────────────
//
// Mirrors `static inline void dec(lean_object*, lean_object*&)` in object.cpp.

#[inline(always)]
unsafe fn dec_for_del(o: *mut LeanObject, todo: &mut *mut LeanObject) {
    if lean_is_scalar(o) {
        return;
    }
    let rc = (*o).rc;
    if rc > 1 {
        (*o).rc = rc - 1;
    } else if rc == 1 {
        push_back(todo, o);
    } else if rc == 0 {
        // Persistent object — do nothing.
    } else {
        // Multi-threaded object (rc < 0, stored as negative).
        // atomic fetch_add(+1); if the result was -1 we were the last ref.
        let rc_ptr = &raw mut (*o).rc as *mut core::sync::atomic::AtomicI32;
        let prev = (*rc_ptr).fetch_add(1, Ordering::AcqRel);
        if prev == -1 {
            push_back(todo, o);
        }
    }
}

// ─── Core deletion dispatch ───────────────────────────────────────────────────

unsafe fn lean_del_core_other(o: *mut LeanObject, tag: u8, todo: &mut *mut LeanObject) {
    match tag {
        LEAN_CLOSURE_TAG => {
            let n = lean_closure_num_fixed(o) as usize;
            let it = lean_closure_arg_cptr(o);
            for i in 0..n {
                dec_for_del(*it.add(i), todo);
            }
            lean_dealloc(o, lean_closure_byte_size(o));
        }
        LEAN_ARRAY_TAG => {
            let n = lean_array_size(o);
            let it = lean_array_cptr(o);
            for i in 0..n {
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
            // C++ destructs the mpz value then calls lean_free_small_object.
            lean_runtime_free_mpz_object(o);
        }
        LEAN_THUNK_TAG => {
            let t = o as *mut LeanThunkObject;
            if !(*t).m_closure.is_null() {
                dec_for_del((*t).m_closure, todo);
            }
            if !(*t).m_value.is_null() {
                dec_for_del((*t).m_value, todo);
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
            deactivate_task(o);
        }
        LEAN_PROMISE_TAG => {
            deactivate_promise(o);
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

unsafe fn lean_del_core(o: *mut LeanObject, todo: &mut *mut LeanObject) {
    let tag = lean_ptr_tag(o);
    if tag <= LEAN_MAX_CTOR_TAG {
        // Constructor: dec all object fields.
        let n = lean_ctor_num_objs(o) as usize;
        let it = lean_ctor_obj_cptr(o);
        for i in 0..n {
            dec_for_del(*it.add(i), todo);
        }
        lean_free_small_object(o);
    } else {
        lean_del_core_other(o, tag, todo);
    }
}

// ─── Public: lean_free_object ─────────────────────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_free_object(o: *mut LeanObject) {
    match lean_ptr_tag(o) {
        LEAN_ARRAY_TAG        => lean_dealloc(o, lean_array_byte_size(o)),
        LEAN_SCALAR_ARRAY_TAG => lean_dealloc(o, lean_sarray_byte_size(o)),
        LEAN_STRING_TAG       => lean_dealloc(o, lean_string_byte_size(o)),
        LEAN_CLOSURE_TAG      => lean_dealloc(o, lean_closure_byte_size(o)),
        LEAN_MPZ_TAG          => lean_runtime_free_mpz_object(o),
        _                     => lean_free_small_object(o),
    }
}

// ─── Public: lean_dec_ref_cold ────────────────────────────────────────────────
//
// Called when a non-scalar object's RC is not in the fast-path (rc > 1).
// Either we're the last ST owner (rc == 1) or the last MT owner (atomic
// fetch_add returns -1).

#[no_mangle]
pub unsafe extern "C" fn lean_dec_ref_cold(o: *mut LeanObject) {
    let rc = (*o).rc;
    let should_free = if rc == 1 {
        true
    } else {
        // MT object: rc is negative. Adding +1 (fetch_add) moves toward 0.
        // If the previous value was -1, we are the last reference.
        let rc_ptr = &raw mut (*o).rc as *mut core::sync::atomic::AtomicI32;
        (*rc_ptr).fetch_add(1, Ordering::AcqRel) == -1
    };

    if should_free {
        let mut todo: *mut LeanObject = core::ptr::null_mut();
        let mut cur = o;
        loop {
            lean_del_core(cur, &mut todo);
            if todo.is_null() {
                return;
            }
            cur = pop_back(&mut todo);
        }
    }
}

// ─── Public: lean_alloc_ctor_memory_export ───────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_alloc_ctor_memory_export(sz: usize) -> *mut LeanObject {
    lean_alloc_ctor_memory(sz)
}

// ─── Public: lean_mark_persistent ────────────────────────────────────────────
//
// BFS traversal: sets rc = 0 on every reachable non-persistent object, making
// it "persistent" (never freed, never reference-counted).

#[no_mangle]
pub unsafe extern "C" fn lean_mark_persistent(o: *mut LeanObject) {
    // Use a Vec as the worklist — simpler than the pointer-packing trick used
    // in the deletion loop, because we are not freeing these objects.
    let mut todo: Vec<*mut LeanObject> = Vec::new();
    todo.push(o);

    while let Some(o) = todo.pop() {
        if lean_is_scalar(o) || !lean_has_rc(o) {
            continue;
        }
        (*o).rc = 0; // mark persistent

        // Suppress LSan leak reports if compiled with AddressSanitizer.
        // (We can't call __lsan_ignore_object from Rust without the sanitizer
        // headers, so this is intentionally omitted; add via a C shim if
        // needed.)

        let tag = lean_ptr_tag(o);
        if tag <= LEAN_MAX_CTOR_TAG {
            let n = lean_ctor_num_objs(o) as usize;
            let it = lean_ctor_obj_cptr(o);
            for i in 0..n {
                todo.push(*it.add(i));
            }
        } else {
            match tag {
                LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG | LEAN_MPZ_TAG => {}
                LEAN_EXTERNAL_TAG => {
                    // Allocate a transient closure to drive m_foreach.
                    let fn_obj = lean_alloc_closure(
                        mark_persistent_fn as *mut c_void,
                        1,
                        0,
                    );
                    let e = o as *mut LeanExternalObject;
                    ((*(*e).m_class).m_foreach)((*e).m_data, fn_obj);
                    lean_dec(fn_obj);
                }
                LEAN_TASK_TAG => {
                    todo.push(lean_task_get(o));
                }
                LEAN_PROMISE_TAG => {
                    todo.push((*(o as *mut LeanPromiseObject)).result as *mut LeanObject);
                }
                LEAN_CLOSURE_TAG => {
                    let n = lean_closure_num_fixed(o) as usize;
                    let it = lean_closure_arg_cptr(o);
                    for i in 0..n {
                        todo.push(*it.add(i));
                    }
                }
                LEAN_ARRAY_TAG => {
                    let n = lean_array_size(o);
                    let it = lean_array_cptr(o);
                    for i in 0..n {
                        todo.push(*it.add(i));
                    }
                }
                LEAN_THUNK_TAG => {
                    let t = o as *mut LeanThunkObject;
                    if !(*t).m_closure.is_null() {
                        todo.push((*t).m_closure);
                    }
                    if !(*t).m_value.is_null() {
                        todo.push((*t).m_value);
                    }
                }
                LEAN_REF_TAG => {
                    let r = o as *mut LeanRefObject;
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

// Closure function handed to external objects during lean_mark_persistent.
unsafe extern "C" fn mark_persistent_fn(o: *mut LeanObject) -> *mut LeanObject {
    lean_mark_persistent(o);
    lean_box(0)
}

// ─── Public: lean_mark_mt ────────────────────────────────────────────────────
//
// Converts all reachable ST objects to MT by negating their rc.
// No-op in single-threaded builds (LEAN_MULTI_THREAD not set at compile time
// is indicated by the cfg flag below; in the Rust build we always compile the
// multi-threaded version since the crate enables std).

#[no_mangle]
pub unsafe extern "C" fn lean_mark_mt(o: *mut LeanObject) {
    if lean_is_scalar(o) || !lean_is_st(o) {
        return;
    }

    let mut todo: Vec<*mut LeanObject> = Vec::new();
    todo.push(o);

    while let Some(o) = todo.pop() {
        if lean_is_scalar(o) || !lean_is_st(o) {
            continue;
        }
        // Flip sign: ST rc > 0 becomes MT rc < 0.
        (*o).rc = -(*o).rc;

        let tag = lean_ptr_tag(o);
        if tag <= LEAN_MAX_CTOR_TAG {
            let n = lean_ctor_num_objs(o) as usize;
            let it = lean_ctor_obj_cptr(o);
            for i in 0..n {
                todo.push(*it.add(i));
            }
        } else {
            match tag {
                LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG | LEAN_MPZ_TAG => {}
                LEAN_EXTERNAL_TAG => {
                    let fn_obj = lean_alloc_closure(
                        mark_mt_fn as *mut c_void,
                        1,
                        0,
                    );
                    let e = o as *mut LeanExternalObject;
                    ((*(*e).m_class).m_foreach)((*e).m_data, fn_obj);
                    lean_dec(fn_obj);
                }
                LEAN_TASK_TAG => {
                    todo.push(lean_task_get(o));
                }
                LEAN_PROMISE_TAG => {
                    todo.push((*(o as *mut LeanPromiseObject)).result as *mut LeanObject);
                }
                LEAN_CLOSURE_TAG => {
                    let n = lean_closure_num_fixed(o) as usize;
                    let it = lean_closure_arg_cptr(o);
                    for i in 0..n {
                        todo.push(*it.add(i));
                    }
                }
                LEAN_ARRAY_TAG => {
                    let n = lean_array_size(o);
                    let it = lean_array_cptr(o);
                    for i in 0..n {
                        todo.push(*it.add(i));
                    }
                }
                LEAN_THUNK_TAG => {
                    let t = o as *mut LeanThunkObject;
                    if !(*t).m_closure.is_null() {
                        todo.push((*t).m_closure);
                    }
                    if !(*t).m_value.is_null() {
                        todo.push((*t).m_value);
                    }
                }
                LEAN_REF_TAG => {
                    let r = o as *mut LeanRefObject;
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

// Closure function handed to external objects during lean_mark_mt.
unsafe extern "C" fn mark_mt_fn(o: *mut LeanObject) -> *mut LeanObject {
    lean_mark_mt(o);
    lean_dec(o);
    lean_box(0)
}

// ─── lean_has_rc helper (needed by lean_mark_persistent) ─────────────────────
// Returns true when the object has a live reference count (rc != 0).

