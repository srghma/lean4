/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the Strings section from src/runtime/object.cpp (lines 1949-2486).
// Include from lib.rs: include!("runtime_object_string.rs");

mod runtime_object_string_impl {
    use super::*;
    use core::ffi::c_char;
    use core::mem::size_of;

    extern "C" {
        fn lean_free_object(o: *mut LeanObject);
        fn lean_panic_fn(default_val: *mut LeanObject, msg: *mut LeanObject) -> *mut LeanObject;
    }

    // ── local inline helpers ─────────────────────────────────────────────────────

    #[inline]
    unsafe fn lean_string_capacity(o: *mut LeanObject) -> usize {
        (*(o as *const LeanStringObject)).capacity
    }

    #[inline]
    unsafe fn lean_string_byte_size(o: *mut LeanObject) -> usize {
        size_of::<LeanStringObject>() + lean_string_capacity(o)
    }

    #[inline]
    unsafe fn lean_sarray_elem_size(o: *mut LeanObject) -> usize {
        (*o).other as usize
    }

    #[inline]
    unsafe fn lean_sarray_mut_cptr(o: *mut LeanObject) -> *mut u8 {
        (o as *mut u8).add(size_of::<LeanScalarArray>())
    }

    #[inline]
    unsafe fn lean_is_exclusive(o: *mut LeanObject) -> bool {
        (*o).rc == 1
    }

    #[inline]
    unsafe fn lean_ctor_set(o: *mut LeanObject, i: usize, v: *mut LeanObject) {
        (o.add(1) as *mut *mut LeanObject).add(i).write(v);
    }

    #[inline]
    unsafe fn lean_alloc_ctor(tag: u32, num_objs: usize, scalar_sz: usize) -> *mut LeanObject {
        lean_runtime_alloc_ctor(
            tag as core::ffi::c_uint,
            num_objs as core::ffi::c_uint,
            scalar_sz as core::ffi::c_uint,
        )
    }

    // On 64-bit, UInt32 fits in a Lean scalar.
    #[inline]
    unsafe fn lean_box_uint32(v: u32) -> *mut LeanObject {
        lean_box(v as usize)
    }

    #[inline]
    unsafe fn lean_unbox_uint32(o: *mut LeanObject) -> u32 {
        lean_unbox(o) as u32
    }

    #[inline]
    fn lean_char_default_value() -> u32 {
        b'A' as u32
    }

    const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1;

    #[inline]
    unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {
        if n <= LEAN_MAX_SMALL_NAT {
            lean_box(n)
        } else {
            super::runtime_object_nat_int_impl::lean_big_usize_to_nat(n)
        }
    }

    #[inline]
    unsafe fn lean_nat_add(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(a1) && lean_is_scalar(a2) {
            lean_usize_to_nat(lean_unbox(a1).wrapping_add(lean_unbox(a2)))
        } else {
            super::runtime_object_nat_int_impl::lean_nat_big_add(a1, a2)
        }
    }

    #[inline]
    unsafe fn lean_nat_sub(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(a1) && lean_is_scalar(a2) {
            let n1 = lean_unbox(a1);
            let n2 = lean_unbox(a2);
            lean_box(if n1 < n2 { 0 } else { n1 - n2 })
        } else {
            super::runtime_object_nat_int_impl::lean_nat_big_sub(a1, a2)
        }
    }

    // ── string buffer helpers ───────────────────────────────────────────────────

    #[inline]
    unsafe fn w_string_cstr(o: *mut LeanObject) -> *mut c_char {
        (o as *mut u8).add(size_of::<LeanStringObject>()) as *mut c_char
    }

    #[inline]
    fn mk_capacity(sz: usize) -> usize {
        sz * 2
    }

    unsafe fn string_ensure_capacity(o: *mut LeanObject, extra: usize) -> *mut LeanObject {
        debug_assert!(lean_is_exclusive(o));
        let sz = lean_string_size(o);
        let cap = lean_string_capacity(o);
        if sz + extra > cap {
            let new_o = lean_alloc_string(sz, cap + sz + extra, lean_string_len(o));
            core::ptr::copy_nonoverlapping(lean_string_cstr(o), w_string_cstr(new_o), sz);
            lean_free_object(o);
            new_o
        } else {
            o
        }
    }

    // ── UTF-8 decode helper ──────────────────────────────────────────────────────

    #[inline]
    unsafe fn string_utf8_get_core(str: *const u8, size: usize, i: usize) -> Option<u32> {
        let c = *str.add(i) as u32;
        if (c & 0x80) == 0 {
            return Some(c);
        }
        if (c & 0xe0) == 0xc0 && i + 1 < size {
            let c1 = *str.add(i + 1) as u32;
            let r = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if r >= 0x80 {
                return Some(r);
            }
        }
        if (c & 0xf0) == 0xe0 && i + 2 < size {
            let c1 = *str.add(i + 1) as u32;
            let c2 = *str.add(i + 2) as u32;
            let r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if r >= 0x800 && !(0xD800..=0xDFFF).contains(&r) {
                return Some(r);
            }
        }
        if (c & 0xf8) == 0xf0 && i + 3 < size {
            let c1 = *str.add(i + 1) as u32;
            let c2 = *str.add(i + 2) as u32;
            let c3 = *str.add(i + 3) as u32;
            let r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (0x10000..=0x10FFFF).contains(&r) {
                return Some(r);
            }
        }
        None
    }

    #[inline]
    unsafe fn is_utf8_first_byte(c: u8) -> bool {
        (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0
    }

    // ── lossy UTF-8 recovery ─────────────────────────────────────────────────────

    unsafe fn lean_mk_string_lossy_recover(
        s: *const c_char,
        sz: usize,
        pos: usize,
        i: usize,
    ) -> *mut LeanObject {
        let s = s as *const u8;
        let mut out: Vec<u8> = Vec::from(core::slice::from_raw_parts(s, pos));
        let mut char_count = i;
        let mut start = pos;
        let mut p = pos;
        while p < sz {
            let mut next = p;
            if lean_runtime_validate_utf8_one(s, sz, &mut next) {
                char_count += 1;
                p = next;
            } else {
                out.extend_from_slice(core::slice::from_raw_parts(s.add(start), p - start));
                out.extend_from_slice(b"\xef\xbf\xbd"); // U+FFFD
                p += 1;
                while p < sz && (*s.add(p) & 0xc0) == 0x80 {
                    p += 1;
                }
                start = p;
                char_count += 1; // count the replacement char
            }
        }
        out.extend_from_slice(core::slice::from_raw_parts(s.add(start), sz - start));
        lean_mk_string_unchecked(out.as_ptr() as *const c_char, out.len(), char_count)
    }

    // ════════════════════════════════════════════════════════════════════════════
    // String constructors
    // ════════════════════════════════════════════════════════════════════════════

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_mk_string_unchecked(
        s: *const c_char,
        sz: usize,
        len: usize,
    ) -> *mut LeanObject {
        let rsz = sz + 1;
        let r = lean_alloc_string(rsz, rsz, len);
        core::ptr::copy_nonoverlapping(s, w_string_cstr(r), sz);
        *w_string_cstr(r).add(sz) = 0;
        r
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_mk_string_from_bytes(
        s: *const c_char,
        sz: usize,
    ) -> *mut LeanObject {
        let mut pos: usize = 0;
        let mut i: usize = 0;
        if lean_runtime_validate_utf8(s as *const u8, sz, &mut pos, &mut i) {
            lean_mk_string_unchecked(s, pos, i)
        } else {
            lean_mk_string_lossy_recover(s, sz, pos, i)
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_mk_string_from_bytes_unchecked(
        s: *const c_char,
        sz: usize,
    ) -> *mut LeanObject {
        lean_mk_string_unchecked(s, sz, lean_utf8_n_strlen(s, sz))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_mk_string(s: *const c_char) -> *mut LeanObject {
        let mut len: usize = 0;
        let mut p = s;
        while *p != 0 {
            p = p.add(1);
        }
        let sz = p.offset_from(s) as usize;
        lean_mk_string_from_bytes(s, sz)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_mk_ascii_string_unchecked(s: *const c_char) -> *mut LeanObject {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_decode_lossy_utf8(a: *mut LeanObject) -> *mut LeanObject {
        lean_mk_string_from_bytes(lean_sarray_cptr(a) as *const c_char, lean_sarray_size(a))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_from_utf8_unchecked(
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        let r = lean_mk_string_from_bytes_unchecked(
            lean_sarray_cptr(a) as *const c_char,
            lean_sarray_size(a),
        );
        lean_dec(a);
        r
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_validate_utf8(a: *mut LeanObject) -> u8 {
        let mut pos: usize = 0;
        let mut i: usize = 0;
        lean_runtime_validate_utf8(lean_sarray_cptr(a), lean_sarray_size(a), &mut pos, &mut i) as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_to_utf8(s: *mut LeanObject) -> *mut LeanObject {
        let sz = lean_string_size(s) - 1;
        let r = lean_alloc_sarray(1, sz, sz);
        core::ptr::copy_nonoverlapping(
            lean_string_cstr(s),
            lean_sarray_mut_cptr(r) as *mut c_char,
            sz,
        );
        r
    }

    // ════════════════════════════════════════════════════════════════════════════
    // String push / append
    // ════════════════════════════════════════════════════════════════════════════

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_push(s: *mut LeanObject, c: u32) -> *mut LeanObject {
        let sz = lean_string_size(s);
        let len = lean_string_len(s);
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_append(
        s1: *mut LeanObject,
        s2: *mut LeanObject,
    ) -> *mut LeanObject {
        let sz1 = lean_string_size(s1);
        let sz2 = lean_string_size(s2);
        let len1 = lean_string_len(s1);
        let len2 = lean_string_len(s2);
        let new_len = len1 + len2;
        let new_sz = sz1 + sz2 - 1;
        let r;
        if !lean_is_exclusive(s1) {
            r = lean_alloc_string(new_sz, mk_capacity(new_sz), new_len);
            core::ptr::copy_nonoverlapping(lean_string_cstr(s1), w_string_cstr(r), sz1 - 1);
            lean_dec_ref(s1);
        } else {
            debug_assert!(s1 != s2);
            r = string_ensure_capacity(s1, sz2 - 1);
        }
        core::ptr::copy_nonoverlapping(
            lean_string_cstr(s2),
            w_string_cstr(r).add(sz1 - 1),
            sz2 - 1,
        );
        (*(r as *mut LeanStringObject)).size = new_sz;
        (*(r as *mut LeanStringObject)).len = new_len;
        *w_string_cstr(r).add(new_sz - 1) = 0;
        r
    }

    // ════════════════════════════════════════════════════════════════════════════
    // String comparisons
    // ════════════════════════════════════════════════════════════════════════════

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_eq_cold(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
        let sz = lean_string_size(s1);
        core::slice::from_raw_parts(lean_string_cstr(s1) as *const u8, sz)
            == core::slice::from_raw_parts(lean_string_cstr(s2) as *const u8, sz)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_sarray_eq_cold(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        let len = lean_sarray_elem_size(a1) * lean_sarray_size(a1);
        core::slice::from_raw_parts(lean_sarray_cptr(a1), len)
            == core::slice::from_raw_parts(lean_sarray_cptr(a2), len)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_lt(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
        let sz1 = lean_string_size(s1) - 1;
        let sz2 = lean_string_size(s2) - 1;
        let b1 = core::slice::from_raw_parts(lean_string_cstr(s1) as *const u8, sz1);
        let b2 = core::slice::from_raw_parts(lean_string_cstr(s2) as *const u8, sz2);
        b1 < b2
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_compare(s1: *mut LeanObject, s2: *mut LeanObject) -> u8 {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_get(s: *mut LeanObject, i0: *mut LeanObject) -> u32 {
        if lean_is_scalar(i0) {
            let i = lean_unbox(i0);
            let str = lean_string_cstr(s) as *const u8;
            let size = lean_string_size(s) - 1;
            if i < size {
                if let Some(cp) = string_utf8_get_core(str, size, i) {
                    return cp;
                }
            }
        }
        lean_char_default_value()
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_get_fast_cold(
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_get_opt(
        s: *mut LeanObject,
        i0: *mut LeanObject,
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_get_bang(
        s: *mut LeanObject,
        i0: *mut LeanObject,
    ) -> u32 {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_next(
        s: *mut LeanObject,
        i0: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(i0) {
            return lean_nat_add(i0, lean_box(1));
        }
        let i = lean_unbox(i0);
        let str = lean_string_cstr(s) as *const u8;
        let size = lean_string_size(s) - 1;
        if i >= size {
            return lean_usize_to_nat(i + 1);
        }
        let c = *str.add(i);
        if (c & 0x80) == 0 {
            return lean_box(i + 1);
        }
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_next_fast_cold(i: usize, c: u8) -> *mut LeanObject {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_is_valid_pos(
        s: *mut LeanObject,
        i0: *mut LeanObject,
    ) -> u8 {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_extract(
        s: *mut LeanObject,
        b0: *mut LeanObject,
        e0: *mut LeanObject,
    ) -> *mut LeanObject {
        let empty = || lean_mk_string_unchecked(b"\0".as_ptr() as *const c_char, 0, 0);
        if !lean_is_scalar(b0) || !lean_is_scalar(e0) {
            return s;
        }
        let mut b = lean_unbox(b0);
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_prev(
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_utf8_set(
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
        let len = lean_string_len(s);
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_hash(s: *mut LeanObject) -> u64 {
        let sz = lean_string_size(s) - 1;
        let str = lean_string_cstr(s) as *const u8;
        lean_runtime_hash_str(sz, str, 11)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_memcmp(
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_of_usize(n: usize) -> *mut LeanObject {
        let s = n.to_string();
        lean_mk_string_unchecked(s.as_ptr() as *const c_char, s.len(), s.len())
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Slice helpers (lean_slice is a ctor with fields [string, start, end])
    // ════════════════════════════════════════════════════════════════════════════

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_slice_hash(s: *mut LeanObject) -> u64 {
        let start = lean_unbox(lean_ctor_get(s, 1));
        let end_ = lean_unbox(lean_ctor_get(s, 2));
        let sz = if end_ > start { end_ - start } else { 0 };
        let base = lean_string_cstr(lean_ctor_get(s, 0)).add(start) as *const u8;
        lean_runtime_hash_str(sz, base, 11)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_slice_dec_lt(s1: *mut LeanObject, s2: *mut LeanObject) -> u8 {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_mk(cs: *mut LeanObject) -> *mut LeanObject {
        let mut buf: Vec<u8> = Vec::new();
        let mut o = cs;
        let mut len: usize = 0;
        while !lean_is_scalar(o) {
            let cp = lean_unbox_uint32(lean_ctor_get(o, 0));
            let start = buf.len();
            buf.resize(start + 4, 0);
            let consumed =
                lean_runtime_push_unicode_scalar(buf.as_mut_ptr().add(start) as *mut c_char, cp)
                    as usize;
            buf.truncate(start + consumed);
            o = lean_ctor_get(o, 1);
            len += 1;
        }
        lean_dec(cs);
        lean_mk_string_unchecked(buf.as_ptr() as *const c_char, buf.len(), len)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_string_data(s: *mut LeanObject) -> *mut LeanObject {
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
