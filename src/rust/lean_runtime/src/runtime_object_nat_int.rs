// src/rust/lean_runtime/src/runtime_object_nat_int.rs
// Ported from src/runtime/object.cpp — Natural numbers and Integers section.
// Include from lib.rs: include!("runtime_object_nat_int.rs");
//
// Strategy: all operations delegate to the C++ mpz wrappers (alloc_mpz,
// mpz_value, etc.) via extern "C" shims.  Once runtime_mpz.rs exists and
// exposes a safe Rust mpz API, these can be replaced with pure-Rust code.

mod runtime_object_nat_int_impl {
    use super::*;
    use core::ffi::{c_char, c_int};

    #[repr(C)]
    struct LeanMpzNonGmp {
        m_sign: bool,
        m_size: usize,
        m_digits: *mut u32,
    }

    // ── C++ shims that manipulate mpz_object ────────────────────────────────
    extern "C" {
        // Allocate a new mpz_object wrapping an existing mpz value (C++ side).
        // These are thin C++ functions added in src/runtime/object_shims.cpp:
        //   extern "C" lean_object * lean_shim_alloc_mpz_from_str(const char *);
        //   extern "C" lean_object * lean_shim_mpz_add(lean_object *, lean_object *);
        //   ... etc.
        //
        // For now we use the existing C++ nat/int big* operations directly
        // by forwarding from Rust to them.  The symbols below are the C++ ones
        // that are NOT being removed yet — we just re-export them under the same
        // name by calling through.  When mpz.cpp is ported to Rust we will
        // replace these bodies.
        fn lean_nat_big_succ_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_add_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_sub_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_mul_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_overflow_mul_cxx(a1: usize, a2: usize) -> *mut LeanObject;
        fn lean_nat_big_div_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_div_exact_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_mod_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_eq_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_nat_big_le_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_nat_big_lt_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_nat_big_land_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_lor_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_xor_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_shiftl_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_shiftr_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_pow_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_gcd_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_log2_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_cstr_to_nat_cxx(n: *const c_char) -> *mut LeanObject;
        fn lean_big_usize_to_nat_cxx(n: usize) -> *mut LeanObject;
        fn lean_big_uint64_to_nat_cxx(n: u64) -> *mut LeanObject;
        fn lean_mpz_hash_cxx(o: *mut LeanObject) -> u32;
        fn lean_mpz_eq_cxx(o1: *mut LeanObject, o2: *mut LeanObject) -> u8;
        fn lean_alloc_mpz_from_mpz_cxx(o: *mut LeanObject) -> *mut LeanObject;
        fn lean_uint8_of_big_nat_cxx(a: *mut LeanObject) -> u8;
        fn lean_uint16_of_big_nat_cxx(a: *mut LeanObject) -> u16;
        fn lean_uint32_of_big_nat_cxx(a: *mut LeanObject) -> u32;
        fn lean_uint64_of_big_nat_cxx(a: *mut LeanObject) -> u64;
        fn lean_usize_of_big_nat_cxx(a: *mut LeanObject) -> usize;
        fn lean_int8_of_big_int_cxx(a: *mut LeanObject) -> i8;
        fn lean_int16_of_big_int_cxx(a: *mut LeanObject) -> i16;
        fn lean_int32_of_big_int_cxx(a: *mut LeanObject) -> i32;
        fn lean_int64_of_big_int_cxx(a: *mut LeanObject) -> i64;
        fn lean_isize_of_big_int_cxx(a: *mut LeanObject) -> isize;
        fn lean_int_big_neg_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_add_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_sub_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_mul_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_div_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_div_exact_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_mod_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_ediv_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_emod_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_eq_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_int_big_le_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_int_big_lt_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_int_big_nonneg_cxx(a: *mut LeanObject) -> bool;
        fn lean_big_int_to_nat_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_cstr_to_int_cxx(n: *const c_char) -> *mut LeanObject;
        fn lean_big_int_to_int_cxx(n: c_int) -> *mut LeanObject;
        fn lean_big_size_t_to_int_cxx(n: usize) -> *mut LeanObject;
        fn lean_big_int64_to_int_cxx(n: i64) -> *mut LeanObject;
        fn lean_uint64_mix_hash_cxx(a1: u64, a2: u64) -> u64;
        fn lean_alloc_small_object(size: usize) -> *mut LeanObject;
        fn lean_free_small_object(obj: *mut LeanObject);
        fn lean_set_st_header(obj: *mut LeanObject, tag: u8, other: u8);
        fn lean_sys_alloc(size: usize) -> *mut u8;
        fn lean_sys_free_sized(ptr: *mut u8, size: usize);
        #[cfg(feature = "use_gmp")]
        fn lean_alloc_mpz_gmp(v: *mut core::ffi::c_void) -> *mut LeanObject;
        #[cfg(feature = "use_gmp")]
        fn lean_extract_mpz_value_gmp(o: *mut LeanObject, v: *mut core::ffi::c_void);
    }

    const LEAN_MPZ_TAG: u8 = 250;

    #[cfg(not(lean_use_gmp))]
    unsafe fn alloc_mpz_object() -> *mut LeanObject {
        let obj = lean_alloc_small_object(core::mem::size_of::<LeanMpzNonGmp>()) as *mut LeanObject;
        lean_set_st_header(obj, LEAN_MPZ_TAG, 0);
        obj
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_digits_alloc(size: usize) -> *mut u32 {
        lean_sys_alloc(size * core::mem::size_of::<u32>()) as *mut u32
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_digits_free(ptr: *mut u32, size: usize) {
        lean_sys_free_sized(ptr as *mut u8, size * core::mem::size_of::<u32>());
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_ptr(obj: *mut LeanObject) -> *mut LeanMpzNonGmp {
        obj as *mut LeanMpzNonGmp
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_const_ptr(obj: *mut LeanObject) -> *const LeanMpzNonGmp {
        obj as *const LeanMpzNonGmp
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_from_u128(n: u128) -> *mut LeanObject {
        if n <= (usize::MAX >> 1) as u128 {
            return lean_box(n as usize);
        }
        let obj = alloc_mpz_object();
        let mpz = mpz_ptr(obj);
        (*mpz).m_sign = false;
        if n <= u64::MAX as u128 {
            (*mpz).m_size = if n >> 32 == 0 { 1 } else { 2 };
        } else {
            (*mpz).m_size = if n >> 96 == 0 {
                if n >> 64 == 0 { 2 } else { 3 }
            } else {
                4
            };
        }
        (*mpz).m_digits = mpz_digits_alloc((*mpz).m_size);
        let mut tmp = n;
        for i in 0..(*mpz).m_size {
            *(*mpz).m_digits.add(i) = (tmp & 0xFFFF_FFFF) as u32;
            tmp >>= 32;
        }
        obj
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_to_u128(obj: *mut LeanObject) -> u128 {
        if lean_is_scalar(obj) {
            return lean_unbox(obj) as u128;
        }
        let mpz = mpz_const_ptr(obj);
        let mut value = 0u128;
        let limbs = (*mpz).m_size.min(4);
        for i in (0..limbs).rev() {
            value <<= 32;
            value |= *(*mpz).m_digits.add(i) as u128;
        }
        value
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_to_i128(obj: *mut LeanObject) -> i128 {
        if lean_is_scalar(obj) {
            return lean_unbox(obj) as isize as i128;
        }
        let mpz = mpz_const_ptr(obj);
        let mut value = 0i128;
        let limbs = (*mpz).m_size.min(4);
        for i in (0..limbs).rev() {
            value <<= 32;
            value |= *(*mpz).m_digits.add(i) as i128;
        }
        if (*mpz).m_sign { -value } else { value }
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_from_i128(n: i128) -> *mut LeanObject {
        if n >= isize::MIN as i128 && n <= isize::MAX as i128 {
            return lean_box(n as isize as usize);
        }
        let obj = alloc_mpz_object();
        let mpz = mpz_ptr(obj);
        let magnitude = if n < 0 { (-n) as u128 } else { n as u128 };
        (*mpz).m_sign = n < 0;
        if magnitude <= u64::MAX as u128 {
            (*mpz).m_size = if magnitude >> 32 == 0 { 1 } else { 2 };
        } else {
            (*mpz).m_size = if magnitude >> 96 == 0 {
                if magnitude >> 64 == 0 { 2 } else { 3 }
            } else {
                4
            };
        }
        (*mpz).m_digits = mpz_digits_alloc((*mpz).m_size);
        let mut tmp = magnitude;
        for i in 0..(*mpz).m_size {
            *(*mpz).m_digits.add(i) = (tmp & 0xFFFF_FFFF) as u32;
            tmp >>= 32;
        }
        obj
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_clone(obj: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(obj) {
            obj
        } else {
            let src = mpz_const_ptr(obj);
            let out = alloc_mpz_object();
            let dst = mpz_ptr(out);
            (*dst).m_sign = (*src).m_sign;
            (*dst).m_size = (*src).m_size;
            (*dst).m_digits = mpz_digits_alloc((*src).m_size);
            core::ptr::copy_nonoverlapping((*src).m_digits, (*dst).m_digits, (*src).m_size);
            out
        }
    }

    #[cfg(not(lean_use_gmp))]
    #[inline]
    fn hash_combine(mut h: u64, mut k: u64) -> u64 {
        let m: u64 = 0xc6a4_a793_5bd1_e995;
        let r = 47;
        k = k.wrapping_mul(m);
        k ^= k >> r;
        k ^= m;
        h ^= k;
        h = h.wrapping_mul(m);
        h
    }

    macro_rules! trace_nat_int {
        ($name:literal) => {{
            #[cfg(feature = "std")]
            {
            use core::sync::atomic::{AtomicUsize, Ordering};
            use std::io::Write;
            static COUNT: AtomicUsize = AtomicUsize::new(0);
            if crate::runtime_trace_enabled("LEAN_TRACE_NAT_INT") {
                let n = COUNT.fetch_add(1, Ordering::Relaxed) + 1;
                if n <= 8 || n.is_power_of_two() {
                    if let Ok(mut f) = std::fs::OpenOptions::new()
                        .create(true)
                        .append(true)
                            .open("/tmp/lean_nat_trace.log")
                        {
                            let _ = writeln!(f, "[nat-int] {} {}", $name, n);
                        }
                    }
                }
            }
        }};
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_hash_value(obj: *mut LeanObject) -> u32 {
        if lean_is_scalar(obj) {
            return hash_combine(0, lean_unbox(obj) as u64) as u32;
        }
        let mpz = mpz_const_ptr(obj);
        let mut h = hash_combine(0, (*mpz).m_sign as u64);
        h = hash_combine(h, (*mpz).m_size as u64);
        for i in 0..(*mpz).m_size {
            h = hash_combine(h, *(*mpz).m_digits.add(i) as u64);
        }
        h as u32
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_free(obj: *mut LeanObject) {
        if !lean_is_scalar(obj) {
            let mpz = mpz_ptr(obj);
            if !(*mpz).m_digits.is_null() {
                mpz_digits_free((*mpz).m_digits, (*mpz).m_size);
                (*mpz).m_digits = core::ptr::null_mut();
            }
            lean_free_small_object(obj);
        }
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_from_cstr(n: *const c_char) -> *mut LeanObject {
        let mut value: u128 = 0;
        let mut bytes = core::ffi::CStr::from_ptr(n).to_bytes();
        while let Some(b' ') = bytes.first().copied() {
            bytes = &bytes[1..];
        }
        for &ch in bytes {
            if ch.is_ascii_digit() {
                value = value * 10 + (ch - b'0') as u128;
            }
        }
        mpz_from_u128(value)
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_temp_from_nat(n: *mut LeanObject) -> *mut LeanObject {
        mpz_from_u128(mpz_to_u128(n))
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_to_nat_owned(obj: *mut LeanObject) -> *mut LeanObject {
        let value = mpz_to_u128(obj);
        mpz_free(obj);
        mpz_from_u128(value)
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Natural numbers
    // ════════════════════════════════════════════════════════════════════════════

    #[no_mangle]
    pub unsafe extern "C" fn lean_cstr_to_nat(n: *const c_char) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_cstr_to_nat_cxx(n)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_cstr(n)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_usize_to_nat(n: usize) -> *mut LeanObject {
        if n <= usize::MAX >> 1 {
            lean_box(n)
        } else {
            mpz_from_u128(n as u128)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_uint64_to_nat(n: u64) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_big_uint64_to_nat_cxx(n)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128(n as u128)
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_succ(a: *mut LeanObject) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_succ_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128(mpz_to_u128(a) + 1)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_add(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        trace_nat_int!("lean_nat_big_add");
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_add_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128(mpz_to_u128(a1) + mpz_to_u128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_sub(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_sub_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let lhs = mpz_to_u128(a1);
            let rhs = mpz_to_u128(a2);
            if lhs < rhs { lean_box(0) } else { mpz_from_u128(lhs - rhs) }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_mul(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        trace_nat_int!("lean_nat_big_mul");
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_mul_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128(mpz_to_u128(a1) * mpz_to_u128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_overflow_mul(a1: usize, a2: usize) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_overflow_mul_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128((a1 as u128) * (a2 as u128))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_div(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        trace_nat_int!("lean_nat_big_div");
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_div_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let rhs = mpz_to_u128(a2);
            if rhs == 0 {
                return lean_box(0);
            }
            mpz_from_u128(mpz_to_u128(a1) / rhs)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_div_exact(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_div_exact_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let rhs = mpz_to_u128(a2);
            if rhs == 0 {
                return lean_box(0);
            }
            mpz_from_u128(mpz_to_u128(a1) / rhs)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_mod(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        trace_nat_int!("lean_nat_big_mod");
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_mod_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let rhs = mpz_to_u128(a2);
            if rhs == 0 {
                return a1;
            }
            mpz_from_u128(mpz_to_u128(a1) % rhs)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_eq(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        if a1 == a2 {
            return true;
        }
        if lean_is_scalar(a1) || lean_is_scalar(a2) {
            return false;
        }
        lean_nat_big_eq(a1, a2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_eq(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_eq_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_u128(a1) == mpz_to_u128(a2)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_le(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_le_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_u128(a1) <= mpz_to_u128(a2)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_lt(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_lt_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_u128(a1) < mpz_to_u128(a2)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_land(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_land_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128(mpz_to_u128(a1) & mpz_to_u128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_lor(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_lor_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128(mpz_to_u128(a1) | mpz_to_u128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_xor(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_xor_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_u128(mpz_to_u128(a1) ^ mpz_to_u128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_shiftl(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_shiftl_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let lhs = mpz_to_u128(a1);
            if lhs == 0 {
                return lean_box(0);
            }
            if !lean_is_scalar(a2) || lean_unbox(a2) > u32::MAX as usize {
                lean_internal_panic(b"Nat.shiftl exponent is too big\0".as_ptr() as *const c_char);
            }
            let shift = lean_unbox(a2) as u32;
            if lhs != 0 && shift >= 128 {
                lean_internal_panic(b"Nat.shiftl exponent is too big\0".as_ptr() as *const c_char);
            }
            mpz_from_u128(lhs.checked_shl(shift).unwrap_or(0))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_shiftr(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        trace_nat_int!("lean_nat_big_shiftr");
        #[cfg(lean_use_gmp)]
        {
            lean_nat_big_shiftr_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            if !lean_is_scalar(a2) {
                return lean_box(0);
            }
            let s = lean_unbox(a2);
            let lhs = mpz_to_u128(a1);
            if s > u32::MAX as usize {
                let bits = if lhs == 0 { 0 } else { 128 - lhs.leading_zeros() as usize };
                if bits >= s {
                    lean_internal_panic(b"Nat.shiftr exponent is too big\0".as_ptr() as *const c_char);
                }
                return lean_box(0);
            }
            mpz_from_u128(lhs >> s)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_pow(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        trace_nat_int!("lean_nat_pow");
        #[cfg(lean_use_gmp)]
        {
            lean_nat_pow_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            if !lean_is_scalar(a2) || lean_unbox(a2) > u32::MAX as usize {
                lean_internal_panic(b"Nat.pow exponent is too big\0".as_ptr() as *const c_char);
            }
            mpz_from_u128(mpz_to_u128(a1).pow(lean_unbox(a2) as u32))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_gcd(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_nat_gcd_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let mut x = mpz_to_u128(a1);
            let mut y = mpz_to_u128(a2);
            while y != 0 {
                let t = y;
                y = x % y;
                x = t;
            }
            mpz_from_u128(x)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_log2(a: *mut LeanObject) -> *mut LeanObject {
        trace_nat_int!("lean_nat_log2");
        #[cfg(lean_use_gmp)]
        {
            lean_nat_log2_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            if lean_is_scalar(a) {
                let mut res = 0usize;
                let mut n = lean_unbox(a);
                while n >= 2 {
                    res += 1;
                    n /= 2;
                }
                lean_box(res)
            } else {
                let value = mpz_to_u128(a);
                if value == 0 {
                    lean_box(0)
                } else {
                    lean_box((127 - value.leading_zeros() as u32) as usize)
                }
            }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_mpz_hash(o: *mut LeanObject) -> u32 {
        #[cfg(lean_use_gmp)]
        {
            lean_mpz_hash_cxx(o)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_hash_value(o)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_mpz_eq(
        o1: *mut LeanObject, o2: *mut LeanObject,
    ) -> u8 {
        #[cfg(lean_use_gmp)]
        {
            lean_mpz_eq_cxx(o1, o2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            if lean_is_scalar(o1) && lean_is_scalar(o2) {
                (lean_unbox(o1) == lean_unbox(o2)) as u8
            } else if lean_is_scalar(o1) || lean_is_scalar(o2) {
                0
            } else {
                let a = mpz_const_ptr(o1);
                let b = mpz_const_ptr(o2);
                if (*a).m_sign != (*b).m_sign || (*a).m_size != (*b).m_size {
                    0
                } else if core::ptr::eq((*a).m_digits, (*b).m_digits) {
                    1
                } else {
                    (core::slice::from_raw_parts((*a).m_digits, (*a).m_size)
                        == core::slice::from_raw_parts((*b).m_digits, (*b).m_size)) as u8
                }
            }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_alloc_mpz_from_mpz(o: *mut LeanObject) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_alloc_mpz_from_mpz_cxx(o)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_clone(o)
        }
    }

    // ── UInt truncations ────────────────────────────────────────────────────
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint8_of_big_nat(a: *mut LeanObject) -> u8 {
        #[cfg(lean_use_gmp)]
        {
            lean_uint8_of_big_nat_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_u128(a) as u8
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint16_of_big_nat(a: *mut LeanObject) -> u16 {
        #[cfg(lean_use_gmp)]
        {
            lean_uint16_of_big_nat_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_u128(a) as u16
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint32_of_big_nat(a: *mut LeanObject) -> u32 {
        #[cfg(lean_use_gmp)]
        {
            lean_uint32_of_big_nat_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_u128(a) as u32
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint64_of_big_nat(a: *mut LeanObject) -> u64 {
        #[cfg(lean_use_gmp)]
        {
            lean_uint64_of_big_nat_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            if lean_is_scalar(a) {
                lean_unbox(a) as u64
            } else {
                mpz_to_u128(a) as u64
            }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_usize_of_big_nat(a: *mut LeanObject) -> usize {
        lean_uint64_of_big_nat(a) as usize
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint64_mix_hash(a1: u64, a2: u64) -> u64 {
        #[cfg(lean_use_gmp)]
        {
            lean_uint64_mix_hash_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            hash_combine(a1, a2)
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Integers
    // ════════════════════════════════════════════════════════════════════════════

    #[no_mangle]
    pub unsafe extern "C" fn lean_big_int_to_nat(a: *mut LeanObject) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_big_int_to_nat_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let value = mpz_to_i128(a);
            if value < 0 { lean_box(0) } else { mpz_from_u128(value as u128) }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_cstr_to_int(n: *const c_char) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_cstr_to_int_cxx(n)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_cstr(n)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_int_to_int(n: c_int) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_big_int_to_int_cxx(n)
        }
        #[cfg(not(lean_use_gmp))]
        {
            lean_box(n as usize)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_size_t_to_int(n: usize) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_big_size_t_to_int_cxx(n)
        }
        #[cfg(not(lean_use_gmp))]
        {
            lean_box(n)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_int64_to_int(n: i64) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_big_int64_to_int_cxx(n)
        }
        #[cfg(not(lean_use_gmp))]
        {
            lean_box(n as usize)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_neg(a: *mut LeanObject) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_neg_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_i128(-mpz_to_i128(a))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_add(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_add_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_i128(mpz_to_i128(a1) + mpz_to_i128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_sub(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_sub_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_i128(mpz_to_i128(a1) - mpz_to_i128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_mul(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_mul_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_from_i128(mpz_to_i128(a1) * mpz_to_i128(a2))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_div(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_div_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let rhs = mpz_to_i128(a2);
            if rhs == 0 { lean_box(0) } else { mpz_from_i128(mpz_to_i128(a1) / rhs) }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_div_exact(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_div_exact_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let rhs = mpz_to_i128(a2);
            if rhs == 0 { lean_box(0) } else { mpz_from_i128(mpz_to_i128(a1) / rhs) }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_mod(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_mod_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let rhs = mpz_to_i128(a2);
            if rhs == 0 { lean_box(0) } else { mpz_from_i128(mpz_to_i128(a1) % rhs) }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_ediv(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_ediv_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let lhs = mpz_to_i128(a1);
            let rhs = mpz_to_i128(a2);
            if rhs == 0 {
                lean_box(0)
            } else {
                let q = lhs / rhs;
                let r = lhs % rhs;
                if r != 0 && ((r > 0) != (rhs > 0)) { mpz_from_i128(q - 1) } else { mpz_from_i128(q) }
            }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_emod(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_emod_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            let lhs = mpz_to_i128(a1);
            let rhs = mpz_to_i128(a2);
            if rhs == 0 {
                lean_box(0)
            } else {
                let r = lhs % rhs;
                if r != 0 && ((r > 0) != (rhs > 0)) { mpz_from_i128(r + rhs) } else { mpz_from_i128(r) }
            }
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_eq(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_eq_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a1) == mpz_to_i128(a2)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_le(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_le_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a1) <= mpz_to_i128(a2)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_lt(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_lt_cxx(a1, a2)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a1) < mpz_to_i128(a2)
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_nonneg(a: *mut LeanObject) -> bool {
        #[cfg(lean_use_gmp)]
        {
            lean_int_big_nonneg_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a) >= 0
        }
    }

    // ── IntX truncations ─────────────────────────────────────────────────────
    #[no_mangle]
    pub unsafe extern "C" fn lean_int8_of_big_int(a: *mut LeanObject) -> i8 {
        #[cfg(lean_use_gmp)]
        {
            lean_int8_of_big_int_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a) as i8
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int16_of_big_int(a: *mut LeanObject) -> i16 {
        #[cfg(lean_use_gmp)]
        {
            lean_int16_of_big_int_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a) as i16
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int32_of_big_int(a: *mut LeanObject) -> i32 {
        #[cfg(lean_use_gmp)]
        {
            lean_int32_of_big_int_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a) as i32
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int64_of_big_int(a: *mut LeanObject) -> i64 {
        #[cfg(lean_use_gmp)]
        {
            lean_int64_of_big_int_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a) as i64
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_isize_of_big_int(a: *mut LeanObject) -> isize {
        #[cfg(lean_use_gmp)]
        {
            lean_isize_of_big_int_cxx(a)
        }
        #[cfg(not(lean_use_gmp))]
        {
            mpz_to_i128(a) as isize
        }
    }

    // ── GMP raw interface (when USE_GMP is on) ───────────────────────────────
    #[cfg(feature = "use_gmp")]
    #[no_mangle]
    pub unsafe extern "C" fn lean_alloc_mpz(v: *mut core::ffi::c_void) -> *mut LeanObject {
        lean_alloc_mpz_gmp(v)
    }
    #[cfg(feature = "use_gmp")]
    #[no_mangle]
    pub unsafe extern "C" fn lean_extract_mpz_value(
        o: *mut LeanObject, v: *mut core::ffi::c_void,
    ) {
        lean_extract_mpz_value_gmp(o, v);
    }
}
