/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the Array, ByteArray, and FloatArray exported helpers from
// src/runtime/object.cpp.

mod runtime_object_array_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ffi::{c_int, c_ulong};
    use leanh::{LeanMpzObject, LeanThunkObject};

    unsafe extern "C" {
        fn lean_internal_panic_out_of_memory() -> !;
        fn lean_mk_ascii_string_unchecked(text: *const c_char) -> *mut LeanObject;
        fn lean_hash_str(len: usize, text: *const u8, seed: u64) -> u64;
    }

    #[inline]
    unsafe fn lean_array_capacity(o: *const LeanObject) -> usize {
        (*(o as *const LeanArrayObject)).capacity
    }

    #[inline]
    unsafe fn nat_to_size_t(n: *mut LeanObject) -> usize {
        if lean_is_scalar(n) {
            lean_unbox(n)
        } else {
            let mpz = &(*(n as *const LeanMpzObject)).m_value;
            if (*(mpz.as_ptr()))._mp_size < 0 || __gmpz_size(mpz) > 1 {
                lean_internal_panic_out_of_memory();
            }
            let sz = __gmpz_getlimbn(mpz, 0) as usize;
            lean_dec(n);
            sz
        }
    }

    unsafe fn copy_sarray_with_capacity(a: *mut LeanObject, cap: usize) -> *mut LeanObject {
        let esz = lean_sarray_elem_size(a);
        let sz = lean_sarray_size(a);
        debug_assert!(cap >= sz);
        let r = lean_alloc_sarray(esz as c_uint, sz, cap);
        core::ptr::copy_nonoverlapping(lean_sarray_cptr(a), lean_sarray_mut_cptr(r), esz * sz);
        lean_dec(a);
        r
    }

    pub unsafe fn lean_copy_sarray(a: *mut LeanObject, cap: usize) -> *mut LeanObject {
        copy_sarray_with_capacity(a, cap)
    }

    pub unsafe fn lean_copy_byte_array(a: *mut LeanObject) -> *mut LeanObject {
        copy_sarray_with_capacity(a, lean_sarray_capacity(a))
    }

    pub unsafe fn lean_byte_array_copy_slice(
        src: *mut LeanObject,
        o_src_off: *mut LeanObject,
        dest: *mut LeanObject,
        o_dest_off: *mut LeanObject,
        o_len: *mut LeanObject,
        exact: bool,
    ) -> *mut LeanObject {
        let ssz = lean_sarray_size(src);
        let dsz = lean_sarray_size(dest);
        let src_off = nat_to_size_t(o_src_off);
        if src_off > ssz {
            return dest;
        }
        let len = nat_to_size_t(o_len).min(ssz - src_off);
        let dest_off = nat_to_size_t(o_dest_off).min(dsz);
        let new_dsz = dsz.max(
            dest_off
                .checked_add(len)
                .unwrap_or_else(|| lean_internal_panic_out_of_memory()),
        );
        let r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(dest, new_dsz, exact));
        (*(r as *mut LeanScalarArray)).size = new_dsz;
        core::ptr::copy_nonoverlapping(
            lean_sarray_cptr(src).add(src_off),
            lean_sarray_mut_cptr(r).add(dest_off),
            len,
        );
        r
    }

    pub unsafe fn lean_byte_array_hash(a: *const LeanObject) -> u64 {
        lean_hash_str(lean_sarray_size(a), lean_sarray_cptr(a), 11)
    }

    pub unsafe fn lean_copy_float_array(a: *mut LeanObject) -> *mut LeanObject {
        copy_sarray_with_capacity(a, lean_sarray_capacity(a))
    }

    pub unsafe fn lean_float_array_mk(a: *mut LeanObject) -> *mut LeanObject {
        let sz = lean_array_size(a);
        let r = lean_alloc_sarray(core::mem::size_of::<f64>() as c_uint, sz, sz);
        let src = lean_array_cptr(a);
        let dst = lean_sarray_mut_cptr(r) as *mut f64;
        for i in 0..sz {
            *dst.add(i) = lean_unbox_float(*src.add(i));
        }
        lean_dec(a);
        r
    }

    pub unsafe fn lean_float_array_data(a: *mut LeanObject) -> *mut LeanObject {
        let sz = lean_sarray_size(a);
        let r = lean_alloc_array(sz, sz);
        let src = lean_sarray_cptr(a) as *const f64;
        let dst = lean_array_cptr(r);
        for i in 0..sz {
            *dst.add(i) = lean_box_float(*src.add(i));
        }
        lean_dec(a);
        r
    }

    pub unsafe fn lean_float_array_push(a: *mut LeanObject, d: f64) -> *mut LeanObject {
        let r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(
            a,
            lean_sarray_size(a) + 1,
            false,
        ));
        let sz = &mut (*(r as *mut LeanScalarArray)).size;
        *(lean_sarray_mut_cptr(r) as *mut f64).add(*sz) = d;
        *sz += 1;
        r
    }

    pub unsafe fn lean_mk_array(n: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject {
        let sz = nat_to_size_t(n);
        let r = lean_alloc_array(sz, sz);
        let dst = lean_array_cptr(r);
        for i in 0..sz {
            *dst.add(i) = v;
        }
        if sz == 0 {
            lean_dec(v);
        } else if sz > 1 {
            lean_inc_n(v, sz - 1);
        }
        r
    }

    pub unsafe fn lean_array_set_panic(a: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject {
        lean_dec(v);
        lean_panic_fn(
            a,
            lean_mk_ascii_string_unchecked(c"Error: index out of bounds".as_ptr()),
        )
    }

    pub unsafe fn lean_thunk_get_core(t: *mut LeanObject) -> *mut LeanObject {
        let thunk = t as *mut LeanThunkObject;
        let c = (*thunk).m_closure.swap(ptr::null_mut(), Ordering::AcqRel);
        if !c.is_null() {
            let r = lean_apply_1(c, lean_box(0));
            debug_assert!(!r.is_null());
            debug_assert!((*thunk).m_value.load(Ordering::Acquire).is_null());
            lean_mark_mt(r);
            (*thunk).m_value.store(r, Ordering::Release);
            r
        } else {
            while (*thunk).m_value.load(Ordering::Acquire).is_null() {
                std::thread::yield_now();
            }
            (*thunk).m_value.load(Ordering::Acquire)
        }
    }
}
