/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the Strings section from src/runtime/object.cpp (lines 1949-2486).
// Include from lib.rs: include!("runtime_object_string.rs");

mod runtime_object_string_impl {
    use crate::*;
    use core::ffi::c_char;
    use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
    use core::mem::size_of;
    use leanh::LEAN_MAX_SMALL_NAT;

    unsafe extern "C" {
        fn lean_panic_fn(default_val: *mut LeanObject, msg: *mut LeanObject) -> *mut LeanObject;
    }

    #[inline]
    unsafe fn lean_sarray_elem_size(o: *const LeanObject) -> usize {
        (*o).other as usize
    }

    #[inline]
    unsafe fn lean_nat_sub(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(a1) && lean_is_scalar(a2) {
            let n1 = lean_unbox(a1);
            let n2 = lean_unbox(a2);
            lean_box(if n1 < n2 { 0 } else { n1 - n2 })
        } else {
            crate::runtime_object_nat_int_impl::lean_nat_big_sub(a1, a2)
        }
    }

    pub unsafe fn lean_mk_ascii_string_unchecked(s: *const c_char) -> *mut LeanObject {
        let mut p = s;
        while *p != 0 {
            p = p.add(1);
        }
        let len = p.offset_from(s) as usize;
        lean_mk_string_unchecked(s, len, len)
    }

    // ════════════════════════════════════════════════════════════════════════════
    // String ↔ ByteArray / UTF-8
    // ════════════════════════════════════════════════════════════════════════════

    pub unsafe fn lean_decode_lossy_utf8(a: *mut LeanObject) -> *mut LeanObject {
        lean_mk_string_from_bytes(lean_sarray_cptr(a) as *const c_char, lean_sarray_size(a))
    }

    pub unsafe fn lean_string_from_utf8_unchecked(a: *mut LeanObject) -> *mut LeanObject {
        let r = lean_mk_string_from_bytes_unchecked(
            lean_sarray_cptr(a) as *const c_char,
            lean_sarray_size(a),
        );
        lean_dec(a);
        r
    }

    pub unsafe fn lean_string_validate_utf8(a: *const LeanObject) -> u8 {
        let mut pos: usize = 0;
        let mut i: usize = 0;
        lean_runtime_validate_utf8(lean_sarray_cptr(a), lean_sarray_size(a), &mut pos, &mut i) as u8
    }

    // ════════════════════════════════════════════════════════════════════════════
    // String push / append
    // ════════════════════════════════════════════════════════════════════════════

    pub unsafe fn lean_string_push(s: *mut LeanObject, c: u32) -> *mut LeanObject {
        let sz = lean_string_size(s);
        let len = lean_string_length(s);
        let r;
        if !lean_is_exclusive(s) {
            r = lean_alloc_string(sz, mk_capacity(sz + 5), len);
            core::ptr::copy_nonoverlapping(lean_string_cstr(s), w_string_cstr(r), sz - 1);
            lean_dec_ref(s);
        } else {
            r = string_ensure_capacity(s, 5);
        }
        let consumed = lean_runtime_push_unicode_scalar(w_string_cstr(r).add(sz - 1), c) as usize;
        (*(r as *mut LeanStringObject)).size = sz + consumed;
        (*(r as *mut LeanStringObject)).len += 1;
        *w_string_cstr(r).add(sz + consumed - 1) = 0;
        r
    }

    pub unsafe fn lean_sarray_eq_cold(a1: *const LeanObject, a2: *const LeanObject) -> bool {
        let len = lean_sarray_elem_size(a1) * lean_sarray_size(a1);
        core::slice::from_raw_parts(lean_sarray_cptr(a1), len)
            == core::slice::from_raw_parts(lean_sarray_cptr(a2), len)
    }

    pub unsafe fn lean_string_lt(s1: *const LeanObject, s2: *const LeanObject) -> bool {
        let sz1 = lean_string_size(s1) - 1;
        let sz2 = lean_string_size(s2) - 1;
        let b1 = core::slice::from_raw_parts(lean_string_cstr(s1) as *const u8, sz1);
        let b2 = core::slice::from_raw_parts(lean_string_cstr(s2) as *const u8, sz2);
        b1 < b2
    }

    pub unsafe fn lean_string_compare(s1: *const LeanObject, s2: *const LeanObject) -> u8 {
        let sz1 = lean_string_size(s1) - 1;
        let sz2 = lean_string_size(s2) - 1;
        let b1 = core::slice::from_raw_parts(lean_string_cstr(s1) as *const u8, sz1);
        let b2 = core::slice::from_raw_parts(lean_string_cstr(s2) as *const u8, sz2);
        match b1.cmp(b2) {
            core::cmp::Ordering::Less => 0,
            core::cmp::Ordering::Equal => 1,
            core::cmp::Ordering::Greater => 2,
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // UTF-8 get / next / prev / extract / set
    // ════════════════════════════════════════════════════════════════════════════
    pub unsafe fn lean_string_utf8_get_fast_cold(
        str: *const c_char,
        i: usize,
        size: usize,
        c: u8,
    ) -> u32 {
        let c = c as u32;
        if (c & 0xe0) == 0xc0 && i + 1 < size {
            let c1 = *(str as *const u8).add(i + 1) as u32;
            let r = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if r >= 0x80 {
                return r;
            }
        }
        if (c & 0xf0) == 0xe0 && i + 2 < size {
            let c1 = *(str as *const u8).add(i + 1) as u32;
            let c2 = *(str as *const u8).add(i + 2) as u32;
            let r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if r >= 0x800 && !(0xD800..=0xDFFF).contains(&r) {
                return r;
            }
        }
        if (c & 0xf8) == 0xf0 && i + 3 < size {
            let c1 = *(str as *const u8).add(i + 1) as u32;
            let c2 = *(str as *const u8).add(i + 2) as u32;
            let c3 = *(str as *const u8).add(i + 3) as u32;
            let r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (0x10000..=0x10FFFF).contains(&r) {
                return r;
            }
        }
        lean_char_default_value()
    }

    pub unsafe fn lean_string_utf8_get_opt(
        s: *const LeanObject,
        i0: *const LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(i0) {
            let i = lean_unbox(i0);
            let str = lean_string_cstr(s) as *const u8;
            let size = lean_string_size(s) - 1;
            if i < size {
                if let Some(cp) = string_utf8_get_core(str, size, i) {
                    let r = lean_alloc_ctor(1, 1, 0);
                    lean_ctor_set(r, 0, lean_box_uint32(cp));
                    return r;
                }
            }
        }
        lean_box(0)
    }

    unsafe fn string_utf8_get_panic() -> u32 {
        lean_panic_fn(
            lean_box(0),
            lean_mk_ascii_string_unchecked(
                b"Error: invalid `String.Pos` at `String.get!`\0".as_ptr() as *const c_char,
            ),
        );
        lean_char_default_value()
    }

    pub unsafe fn lean_string_utf8_get_bang(s: *const LeanObject, i0: *const LeanObject) -> u32 {
        if lean_is_scalar(i0) {
            let i = lean_unbox(i0);
            let str = lean_string_cstr(s) as *const u8;
            let size = lean_string_size(s) - 1;
            if i < size {
                return string_utf8_get_core(str, size, i)
                    .unwrap_or_else(|| string_utf8_get_panic());
            }
        }
        string_utf8_get_panic()
    }

    pub unsafe fn lean_string_utf8_next_fast_cold(i: usize, c: u8) -> *mut LeanObject {
        if (c & 0xe0) == 0xc0 {
            return lean_box(i + 2);
        }
        if (c & 0xf0) == 0xe0 {
            return lean_box(i + 3);
        }
        if (c & 0xf8) == 0xf0 {
            return lean_box(i + 4);
        }
        lean_box(i + 1)
    }

    pub unsafe fn lean_string_is_valid_pos(s: *const LeanObject, i0: *const LeanObject) -> u8 {
        if !lean_is_scalar(i0) {
            return 0;
        }
        let i = lean_unbox(i0);
        let sz = lean_string_size(s) - 1;
        if i > sz {
            return 0;
        }
        if i == sz {
            return 1;
        }
        let str = lean_string_cstr(s) as *const u8;
        is_utf8_first_byte(*str.add(i)) as u8
    }

    pub unsafe fn lean_string_utf8_extract(
        s: *mut LeanObject,
        b0: *mut LeanObject,
        e0: *mut LeanObject,
    ) -> *mut LeanObject {
        let empty = || lean_mk_string_unchecked(b"\0".as_ptr() as *const c_char, 0, 0);
        if !lean_is_scalar(b0) || !lean_is_scalar(e0) {
            return s;
        }
        let b = lean_unbox(b0);
        let mut e = lean_unbox(e0);
        let str = lean_string_cstr(s) as *const u8;
        let sz = lean_string_size(s) - 1;
        if b >= e || b >= sz {
            return empty();
        }
        if !is_utf8_first_byte(*str.add(b)) {
            return empty();
        }
        if e > sz {
            e = sz;
        }
        if e < sz && !is_utf8_first_byte(*str.add(e)) {
            e = sz;
        }
        let new_sz = e - b;
        lean_mk_string_from_bytes_unchecked(lean_string_cstr(s).add(b), new_sz)
    }

    pub unsafe fn lean_string_utf8_prev(
        s: *mut LeanObject,
        i0: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(i0) {
            return lean_nat_sub(i0, lean_box(1));
        }
        let mut i = lean_unbox(i0);
        let sz = lean_string_size(s) - 1;
        if i == 0 {
            return lean_box(0);
        }
        if i > sz {
            return lean_box(i - 1);
        }
        i -= 1;
        let str = lean_string_cstr(s) as *const u8;
        while !is_utf8_first_byte(*str.add(i)) {
            debug_assert!(i > 0);
            i -= 1;
        }
        lean_box(i)
    }

    pub unsafe fn lean_string_utf8_set(
        s: *mut LeanObject,
        i0: *mut LeanObject,
        c: u32,
    ) -> *mut LeanObject {
        if !lean_is_scalar(i0) {
            return s;
        }
        let i = lean_unbox(i0);
        let sz = lean_string_size(s) - 1;
        if i >= sz {
            return s;
        }
        let str_ptr = w_string_cstr(s);
        if lean_is_exclusive(s) {
            let b = *str_ptr.add(i) as u8;
            if b < 128 && c < 128 {
                *str_ptr.add(i) = c as i8;
                return s;
            }
        }
        if !is_utf8_first_byte(*str_ptr.add(i) as u8) {
            return s;
        }
        let old_c_sz = {
            let b = *str_ptr.add(i) as u8;
            if (b & 0x80) == 0 {
                1
            } else if (b & 0xe0) == 0xc0 {
                2
            } else if (b & 0xf0) == 0xe0 {
                3
            } else {
                4
            }
        };
        let mut buf = [0i8; 4];
        let new_c_sz = lean_runtime_push_unicode_scalar(buf.as_mut_ptr(), c) as usize;
        let old_data = core::slice::from_raw_parts(lean_string_cstr(s) as *const u8, sz);
        let len = lean_string_length(s);
        lean_dec(s);
        let new_total = sz - old_c_sz + new_c_sz;
        let r = lean_alloc_string(new_total + 1, new_total + 1, len);
        let dst = w_string_cstr(r);
        core::ptr::copy_nonoverlapping(old_data.as_ptr() as *const c_char, dst, i);
        core::ptr::copy_nonoverlapping(buf.as_ptr(), dst.add(i), new_c_sz);
        core::ptr::copy_nonoverlapping(
            old_data.as_ptr().add(i + old_c_sz) as *const c_char,
            dst.add(i + new_c_sz),
            sz - i - old_c_sz,
        );
        *dst.add(new_total) = 0;
        (*(r as *mut LeanStringObject)).size = new_total + 1;
        r
    }

    // ════════════════════════════════════════════════════════════════════════════
    // String hash / memcmp / of_usize
    // ════════════════════════════════════════════════════════════════════════════

    pub unsafe fn lean_string_hash(s: *const LeanObject) -> u64 {
        let sz = lean_string_size(s) - 1;
        let str = lean_string_cstr(s) as *const u8;
        lean_runtime_hash_str(sz, str, 11)
    }

    pub unsafe fn lean_string_memcmp(
        s1: *mut LeanObject,
        s2: *mut LeanObject,
        lstart: *mut LeanObject,
        rstart: *mut LeanObject,
        len: *mut LeanObject,
    ) -> u8 {
        let lbase = lean_string_cstr(s1).add(lean_unbox(lstart));
        let rbase = lean_string_cstr(s2).add(lean_unbox(rstart));
        let l = lean_unbox(len);
        let b1 = core::slice::from_raw_parts(lbase as *const u8, l);
        let b2 = core::slice::from_raw_parts(rbase as *const u8, l);
        (b1 == b2) as u8
    }

    pub unsafe fn lean_string_of_usize(n: usize) -> *mut LeanObject {
        let s = n.to_string();
        lean_mk_string_unchecked(s.as_ptr() as *const c_char, s.len(), s.len())
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Slice helpers (lean_slice is a ctor with fields [string, start, end])
    // ════════════════════════════════════════════════════════════════════════════

    pub unsafe fn lean_slice_hash(s: *const LeanObject) -> u64 {
        let start = lean_unbox(lean_ctor_get(s, 1));
        let end_ = lean_unbox(lean_ctor_get(s, 2));
        let sz = if end_ > start { end_ - start } else { 0 };
        let base = lean_string_cstr(lean_ctor_get(s, 0)).add(start) as *const u8;
        lean_runtime_hash_str(sz, base, 11)
    }

    pub unsafe fn lean_slice_dec_lt(s1: *const LeanObject, s2: *const LeanObject) -> u8 {
        let start1 = lean_unbox(lean_ctor_get(s1, 1));
        let end1 = lean_unbox(lean_ctor_get(s1, 2));
        let start2 = lean_unbox(lean_ctor_get(s2, 1));
        let end2 = lean_unbox(lean_ctor_get(s2, 2));
        let sz1 = if end1 > start1 { end1 - start1 } else { 0 };
        let sz2 = if end2 > start2 { end2 - start2 } else { 0 };
        let base1 = lean_string_cstr(lean_ctor_get(s1, 0)).add(start1) as *const u8;
        let base2 = lean_string_cstr(lean_ctor_get(s2, 0)).add(start2) as *const u8;
        let b1 = core::slice::from_raw_parts(base1, sz1);
        let b2 = core::slice::from_raw_parts(base2, sz2);
        (b1 < b2) as u8
    }

    // ════════════════════════════════════════════════════════════════════════════
    // String ↔ List Char
    // ════════════════════════════════════════════════════════════════════════════
    pub unsafe fn lean_string_data(s: *mut LeanObject) -> *mut LeanObject {
        // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 233 (🔁)
        let sz = lean_string_size(s) - 1;
        let bytes = core::slice::from_raw_parts(lean_string_cstr(s) as *const u8, sz);
        let mut cps: Vec<u32> = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            if let Some(cp) = string_utf8_get_core(bytes.as_ptr(), bytes.len(), i) {
                cps.push(cp);
                let b = bytes[i];
                if (b & 0x80) == 0 {
                    i += 1;
                } else if (b & 0xe0) == 0xc0 {
                    i += 2;
                } else if (b & 0xf0) == 0xe0 {
                    i += 3;
                } else {
                    i += 4;
                }
            } else {
                i += 1;
            }
        }
        lean_dec_ref(s);
        let mut r = lean_box(0); // nil
        for &cp in cps.iter().rev() {
            let node = lean_alloc_ctor(1, 2, 0);
            lean_ctor_set(node, 0, lean_box_uint32(cp));
            lean_ctor_set(node, 1, r);
            r = node;
        }
        r
    }
}
