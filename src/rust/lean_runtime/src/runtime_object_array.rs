// src/rust/lean_runtime/src/runtime_object_array.rs
// Ported from src/runtime/object.cpp — Array, ByteArray, FloatArray section.
// Include from lib.rs: include!("runtime_object_array.rs");

mod runtime_object_array_impl {
    use super::*;
    use core::ffi::c_uint;

    extern "C" {
        fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject;
        fn lean_alloc_sarray(elem_size: c_uint, size: usize, capacity: usize) -> *mut LeanObject;
        fn lean_array_size(o: *mut LeanObject) -> usize;
        fn lean_array_capacity(o: *mut LeanObject) -> usize;
        fn lean_array_cptr(o: *mut LeanObject) -> *mut *mut LeanObject;
        fn lean_array_byte_size(o: *mut LeanObject) -> usize;
        fn lean_sarray_size(o: *mut LeanObject) -> usize;
        fn lean_sarray_capacity(o: *mut LeanObject) -> usize;
        fn lean_sarray_elem_size(o: *mut LeanObject) -> c_uint;
        fn lean_sarray_cptr(o: *mut LeanObject) -> *mut u8;
        fn lean_sarray_byte_size(o: *mut LeanObject) -> usize;
        fn lean_is_exclusive(o: *mut LeanObject) -> bool;
        fn lean_is_scalar(o: *mut LeanObject) -> bool;
        fn lean_unbox(o: *mut LeanObject) -> usize;
        fn lean_box(n: usize) -> *mut LeanObject;
        fn lean_box_float(v: f64) -> *mut LeanObject;
        fn lean_unbox_float(o: *mut LeanObject) -> f64;
        fn lean_inc(o: *mut LeanObject);
        fn lean_inc_n(o: *mut LeanObject, n: usize);
        fn lean_dec(o: *mut LeanObject);
        fn lean_dec_ref(o: *mut LeanObject);
        fn lean_internal_panic_out_of_memory() -> !;
        fn lean_dealloc_export(o: *mut LeanObject, sz: usize);
        fn lean_nat_to_size_t(n: *mut LeanObject) -> usize;
        // mpz path for lean_mk_array
        fn lean_internal_panic(msg: *const core::ffi::c_char) -> !;
        fn lean_list_to_array(nil: *mut LeanObject, lst: *mut LeanObject) -> *mut LeanObject;
        fn lean_array_to_list_impl(nil: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;
        fn lean_panic_fn(def: *mut LeanObject, msg: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_ascii_string_unchecked(s: *const core::ffi::c_char) -> *mut LeanObject;
    }

    unsafe fn lean_dealloc(o: *mut LeanObject, sz: usize) {
        lean_dealloc_export(o, sz);
    }

    unsafe fn array_obj(o: *mut LeanObject) -> *mut LeanArrayObject {
        o as *mut LeanArrayObject
    }

    unsafe fn sarray_obj(o: *mut LeanObject) -> *mut LeanScalarArray {
        o as *mut LeanScalarArray
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Array of objects
    // ════════════════════════════════════════════════════════════════════════════

    #[no_mangle]
    pub unsafe extern "C" fn lean_array_mk(lst: *mut LeanObject) -> *mut LeanObject {
        lean_list_to_array(lean_box(0), lst)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_array_to_list(a: *mut LeanObject) -> *mut LeanObject {
        lean_array_to_list_impl(lean_box(0), a)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_array_get_panic(def_val: *mut LeanObject) -> *mut LeanObject {
        lean_panic_fn(def_val, lean_mk_ascii_string_unchecked(
            b"Error: index out of bounds\0".as_ptr() as *const core::ffi::c_char,
        ))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_array_set_panic(
        a: *mut LeanObject, v: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_dec(v);
        lean_panic_fn(a, lean_mk_ascii_string_unchecked(
            b"Error: index out of bounds\0".as_ptr() as *const core::ffi::c_char,
        ))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_array(
        n: *mut LeanObject, v: *mut LeanObject,
    ) -> *mut LeanObject {
        let sz = lean_nat_to_size_t(n);
        let r  = lean_alloc_array(sz, sz);
        let it = lean_array_cptr(r);
        for k in 0..sz {
            *it.add(k) = v;
        }
        if sz == 0 {
            lean_dec(v);
        } else if sz > 1 {
            lean_inc_n(v, sz - 1);
        }
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_copy_expand_array(
        a: *mut LeanObject, expand: bool,
    ) -> *mut LeanObject {
        let sz  = lean_array_size(a);
        let mut cap = lean_array_capacity(a);
        if expand { cap = (cap + 1) * 2; }
        let r    = lean_alloc_array(sz, cap);
        let src  = lean_array_cptr(a);
        let dst  = lean_array_cptr(r);
        if lean_is_exclusive(a) {
            // transfer ownership
            core::ptr::copy_nonoverlapping(src, dst, sz);
            lean_dealloc(a, lean_array_byte_size(a));
        } else {
            for k in 0..sz {
                *dst.add(k) = *src.add(k);
                lean_inc(*src.add(k));
            }
            lean_dec(a);
        }
        r
    }

    #[no_mangle]
    #[inline(never)]
    pub unsafe extern "C" fn lean_copy_expand_array_nonlinear(
        a: *mut LeanObject, expand: bool,
    ) -> *mut LeanObject {
        lean_copy_expand_array(a, expand)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_array_push(
        a: *mut LeanObject, v: *mut LeanObject,
    ) -> *mut LeanObject {
        let r;
        if lean_is_exclusive(a) {
            if lean_array_capacity(a) > lean_array_size(a) {
                r = a;
            } else {
                r = lean_copy_expand_array(a, true);
            }
        } else {
            let expand = lean_array_capacity(a) < 2 * lean_array_size(a) + 1;
            r = lean_copy_expand_array_nonlinear(a, expand);
        }
        let sz_ref = &mut (*array_obj(r)).m_size;
        let it     = lean_array_cptr(r).add(*sz_ref);
        *it = v;
        *sz_ref += 1;
        r
    }

    // ════════════════════════════════════════════════════════════════════════════
    // ByteArray (sarray of u8, elem_size=1)
    // ════════════════════════════════════════════════════════════════════════════

    #[no_mangle]
    pub unsafe extern "C" fn lean_copy_sarray(
        a: *mut LeanObject, cap: usize,
    ) -> *mut LeanObject {
        let esz  = lean_sarray_elem_size(a);
        let sz   = lean_sarray_size(a);
        debug_assert!(cap >= sz);
        let r = lean_alloc_sarray(esz, sz, cap);
        core::ptr::copy_nonoverlapping(lean_sarray_cptr(a), lean_sarray_cptr(r), esz as usize * sz);
        lean_dec(a);
        r
    }

    /// Make sarray exclusive (copy if shared)
    unsafe fn lean_sarray_ensure_exclusive(a: *mut LeanObject) -> *mut LeanObject {
        if lean_is_exclusive(a) { a } else { lean_copy_sarray(a, lean_sarray_capacity(a)) }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_sarray_ensure_capacity(
        a: *mut LeanObject, min_cap: usize, exact: bool,
    ) -> *mut LeanObject {
        let cap = lean_sarray_capacity(a);
        if min_cap <= cap {
            a
        } else {
            lean_copy_sarray(a, if exact { min_cap } else { min_cap * 2 })
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_copy_byte_array(a: *mut LeanObject) -> *mut LeanObject {
        lean_copy_sarray(a, lean_sarray_capacity(a))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_empty_byte_array(capacity: *mut LeanObject) -> *mut LeanObject {
        if !lean_is_scalar(capacity) {
            lean_internal_panic_out_of_memory();
        }
        lean_alloc_sarray(1, 0, lean_unbox(capacity))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_size(a: *mut LeanObject) -> *mut LeanObject {
        lean_box(lean_sarray_size(a))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_uget(a: *mut LeanObject, i: usize) -> u8 {
        *lean_sarray_cptr(a).add(i)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_fget(a: *mut LeanObject, i: *mut LeanObject) -> u8 {
        lean_byte_array_uget(a, lean_unbox(i))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_get(a: *mut LeanObject, i: *mut LeanObject) -> u8 {
        if lean_is_scalar(i) {
            let idx = lean_unbox(i);
            if idx < lean_sarray_size(a) {
                return lean_byte_array_uget(a, idx);
            }
        }
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_uset(
        a: *mut LeanObject,
        i: usize,
        b: u8,
    ) -> *mut LeanObject {
        let r = lean_sarray_ensure_exclusive(a);
        *lean_sarray_cptr(r).add(i) = b;
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_fset(
        a: *mut LeanObject,
        i: *mut LeanObject,
        b: u8,
    ) -> *mut LeanObject {
        lean_byte_array_uset(a, lean_unbox(i), b)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_set(
        a: *mut LeanObject,
        i: *mut LeanObject,
        b: u8,
    ) -> *mut LeanObject {
        if lean_is_scalar(i) {
            let idx = lean_unbox(i);
            if idx < lean_sarray_size(a) {
                return lean_byte_array_uset(a, idx, b);
            }
        }
        a
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_mk(a: *mut LeanObject) -> *mut LeanObject {
        let sz   = lean_array_size(a);
        let r    = lean_alloc_sarray(1, sz, sz);
        let src  = lean_array_cptr(a);
        let dst  = lean_sarray_cptr(r);
        for k in 0..sz {
            *dst.add(k) = lean_unbox(*src.add(k)) as u8;
        }
        lean_dec(a);
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_data(a: *mut LeanObject) -> *mut LeanObject {
        let sz   = lean_sarray_size(a);
        let r    = lean_alloc_array(sz, sz);
        let src  = lean_sarray_cptr(a);
        let dst  = lean_array_cptr(r);
        for k in 0..sz {
            *dst.add(k) = lean_box(*src.add(k) as usize);
        }
        lean_dec(a);
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_push(
        a: *mut LeanObject, b: u8,
    ) -> *mut LeanObject {
        let r = lean_sarray_ensure_exclusive(
            lean_sarray_ensure_capacity(a, lean_sarray_size(a) + 1, false),
        );
        let sz = &mut (*sarray_obj(r)).m_size;
        *lean_sarray_cptr(r).add(*sz) = b;
        *sz += 1;
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_copy_slice(
        src: *mut LeanObject,
        o_src_off: *mut LeanObject,
        dest: *mut LeanObject,
        o_dest_off: *mut LeanObject,
        o_len: *mut LeanObject,
        exact: bool,
    ) -> *mut LeanObject {
        let ssz     = lean_sarray_size(src);
        let dsz     = lean_sarray_size(dest);
        let src_off = lean_nat_to_size_t(o_src_off);
        if src_off > ssz { return dest; }
        let len_req  = lean_nat_to_size_t(o_len);
        let len      = (ssz - src_off).min(len_req);
        let dest_off = lean_nat_to_size_t(o_dest_off).min(dsz);
        let new_dsz  = dsz.max(dest_off + len);
        let r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(dest, new_dsz, exact));
        (*sarray_obj(r)).m_size = new_dsz;
        core::ptr::copy_nonoverlapping(
            lean_sarray_cptr(src).add(src_off),
            lean_sarray_cptr(r).add(dest_off),
            len,
        );
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_byte_array_hash(a: *mut LeanObject) -> u64 {
        extern "C" { fn hash_str(sz: usize, data: *const u8, init: u64) -> u64; }
        hash_str(lean_sarray_size(a), lean_sarray_cptr(a), 11)
    }

    // ════════════════════════════════════════════════════════════════════════════
    // FloatArray (sarray of f64, elem_size=8)
    // ════════════════════════════════════════════════════════════════════════════

    #[no_mangle]
    pub unsafe extern "C" fn lean_copy_float_array(a: *mut LeanObject) -> *mut LeanObject {
        lean_copy_sarray(a, lean_sarray_capacity(a))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_empty_float_array(capacity: *mut LeanObject) -> *mut LeanObject {
        if !lean_is_scalar(capacity) {
            lean_internal_panic_out_of_memory();
        }
        lean_alloc_sarray(core::mem::size_of::<f64>() as c_uint, 0, lean_unbox(capacity))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_size(a: *mut LeanObject) -> *mut LeanObject {
        lean_box(lean_sarray_size(a))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_uget(a: *mut LeanObject, i: usize) -> f64 {
        *((lean_sarray_cptr(a) as *const f64).add(i))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_fget(a: *mut LeanObject, i: *mut LeanObject) -> f64 {
        lean_float_array_uget(a, lean_unbox(i))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_get(a: *mut LeanObject, i: *mut LeanObject) -> f64 {
        if lean_is_scalar(i) {
            let idx = lean_unbox(i);
            if idx < lean_sarray_size(a) {
                return lean_float_array_uget(a, idx);
            }
        }
        0.0
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_uset(
        a: *mut LeanObject,
        i: usize,
        d: f64,
    ) -> *mut LeanObject {
        let r = lean_sarray_ensure_exclusive(a);
        *((lean_sarray_cptr(r) as *mut f64).add(i)) = d;
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_fset(
        a: *mut LeanObject,
        i: *mut LeanObject,
        d: f64,
    ) -> *mut LeanObject {
        lean_float_array_uset(a, lean_unbox(i), d)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_set(
        a: *mut LeanObject,
        i: *mut LeanObject,
        d: f64,
    ) -> *mut LeanObject {
        if lean_is_scalar(i) {
            let idx = lean_unbox(i);
            if idx < lean_sarray_size(a) {
                return lean_float_array_uset(a, idx, d);
            }
        }
        a
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_mk(a: *mut LeanObject) -> *mut LeanObject {
        let sz  = lean_array_size(a);
        let r   = lean_alloc_sarray(core::mem::size_of::<f64>() as c_uint, sz, sz);
        let src = lean_array_cptr(a);
        let dst = lean_sarray_cptr(r) as *mut f64;
        for k in 0..sz {
            *dst.add(k) = lean_unbox_float(*src.add(k));
        }
        lean_dec(a);
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_data(a: *mut LeanObject) -> *mut LeanObject {
        let sz  = lean_sarray_size(a);
        let r   = lean_alloc_array(sz, sz);
        let src = lean_sarray_cptr(a) as *const f64;
        let dst = lean_array_cptr(r);
        for k in 0..sz {
            *dst.add(k) = lean_box_float(*src.add(k));
        }
        lean_dec(a);
        r
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_float_array_push(
        a: *mut LeanObject, d: f64,
    ) -> *mut LeanObject {
        let r = lean_sarray_ensure_exclusive(
            lean_sarray_ensure_capacity(a, lean_sarray_size(a) + 1, false),
        );
        let sz  = &mut (*sarray_obj(r)).m_size;
        let dst = (lean_sarray_cptr(r) as *mut f64).add(*sz);
        *dst = d;
        *sz += 1;
        r
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Thunk get (used in object.cpp near arrays section)
    // ════════════════════════════════════════════════════════════════════════════

    extern "C" {
        fn lean_apply_1(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;
        fn lean_mark_mt(o: *mut LeanObject);
        fn lean_io_result_is_ok(r: *mut LeanObject) -> bool;
        // lean_to_thunk fields
        fn lean_thunk_get_core_impl_cxx(t: *mut LeanObject) -> *mut LeanObject;
    }

    // lean_thunk_get_core is complex (involves atomic exchange + spin wait).
    // We delegate to the C++ implementation until lean_to_thunk layout is
    // fully stable in Rust.
    #[no_mangle]
    pub unsafe extern "C" fn lean_thunk_get_core(t: *mut LeanObject) -> *mut LeanObject {
        lean_thunk_get_core_impl_cxx(t)
    }

}
