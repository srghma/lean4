#![allow(non_camel_case_types, non_snake_case)]

use core::ffi::*;
use core::sync::atomic::{AtomicI32, Ordering};

// ===== TYPES =====

#[repr(C)]
pub struct lean_object {
    pub m_rc: i32,
    pub m_cs_sz: u16,
    pub m_other: u8,
    pub m_tag: u8,
}

#[repr(C)]
pub struct lean_once_cell {
    pub state: i32,
    pub lock: i32,
}

// ===== MACROS =====

/// Declares lean_apply_1..16 in a single extern "C" block.
macro_rules! lean_apply_fns {
    ($($name:ident ($($arg:ident),*));* $(;)?) => {
        extern "C" {
            $(
                pub fn $name(obj: *mut lean_object, $($arg: *mut lean_object),*) -> *mut lean_object;
            )*
        }
    };
}

/// Byte-offset based scalar field get/set on constructor objects.
/// usize uses an index-based accessor and is defined separately.
macro_rules! lean_ctor_scalar_accessors {
    ($($get:ident, $set:ident => $t:ty);* $(;)?) => {
        $(
            #[inline(always)]
            pub unsafe fn $get(o: *mut lean_object, offset: c_uint) -> $t {
                let base = lean_ctor_obj_cptr(o) as *const u8;
                core::ptr::read_unaligned(base.add(offset as usize) as *const $t)
            }
            #[inline(always)]
            pub unsafe fn $set(o: *mut lean_object, offset: c_uint, v: $t) {
                let base = lean_ctor_obj_cptr(o) as *mut u8;
                core::ptr::write_unaligned(base.add(offset as usize) as *mut $t, v);
            }
        )*
    };
}

/// Box/unbox for heap-allocated scalar types (u64, f64, f32).
/// u32 fits in a tagged pointer and is defined manually.
/// usize is conditional and defined manually.
macro_rules! lean_heap_boxing {
    ($($unbox:ident, $box_fn:ident => $t:ty, $get:ident, $set:ident);* $(;)?) => {
        $(
            #[inline(always)]
            pub unsafe fn $box_fn(v: $t) -> *mut lean_object {
                let r = lean_alloc_ctor(0, 0, core::mem::size_of::<$t>() as c_uint);
                $set(r, 0, v);
                r
            }
            #[inline(always)]
            pub unsafe fn $unbox(o: *mut lean_object) -> $t {
                let r = $get(o, 0);
                lean_dec(o);
                r
            }
        )*
    };
}

/// Once-cell fast paths for scalar types.
/// lean_obj_once has a different loc type (*mut *mut lean_object) and is defined manually.
macro_rules! lean_once_fns {
    ($($name:ident, $cold:ident => $t:ty);* $(;)?) => {
        $(
            #[inline(always)]
            pub unsafe fn $name(
                loc: *mut $t,
                tok: *mut lean_once_cell,
                init: unsafe extern "C" fn() -> $t,
            ) -> $t {
                if AtomicI32::from_ptr(&raw mut (*tok).state).load(Ordering::Relaxed) == 1 {
                    *loc
                } else {
                    $cold(loc, tok, init)
                }
            }
        )*
    };
}

/// Arithmetic, bitwise, and comparison ops for u8/u32/u64.
/// Does NOT generate lean_uXX_to_nat — those are defined manually because
/// u64's version differs from u8/u32 on 32-bit targets.
macro_rules! lean_uint_ops {
    (
        $t:ty, $bits:literal,
        $of_nat:ident, $of_big_nat:ident,
        $add:ident, $sub:ident, $mul:ident, $div:ident, $mod_:ident,
        $land:ident, $lor:ident, $xor:ident, $shl:ident, $shr:ident,
        $comp:ident, $neg:ident,
        $eq:ident, $lt:ident, $le:ident
    ) => {
        #[inline(always)]
        pub unsafe fn $of_nat(a: *mut lean_object) -> $t {
            if lean_is_scalar(a as *const lean_object) != 0 {
                lean_unbox(a) as $t
            } else {
                $of_big_nat(a)
            }
        }
        #[inline(always)]
        pub unsafe fn $add(a1: $t, a2: $t) -> $t {
            a1.wrapping_add(a2)
        }
        #[inline(always)]
        pub unsafe fn $sub(a1: $t, a2: $t) -> $t {
            a1.wrapping_sub(a2)
        }
        #[inline(always)]
        pub unsafe fn $mul(a1: $t, a2: $t) -> $t {
            a1.wrapping_mul(a2)
        }
        #[inline(always)]
        pub unsafe fn $div(a1: $t, a2: $t) -> $t {
            if a2 == 0 {
                0
            } else {
                a1 / a2
            }
        }
        #[inline(always)]
        pub unsafe fn $mod_(a1: $t, a2: $t) -> $t {
            if a2 == 0 {
                a1
            } else {
                a1 % a2
            }
        }
        #[inline(always)]
        pub unsafe fn $land(a: $t, b: $t) -> $t {
            a & b
        }
        #[inline(always)]
        pub unsafe fn $lor(a: $t, b: $t) -> $t {
            a | b
        }
        #[inline(always)]
        pub unsafe fn $xor(a: $t, b: $t) -> $t {
            a ^ b
        }
        #[inline(always)]
        pub unsafe fn $shl(a: $t, b: $t) -> $t {
            a << (b % $bits)
        }
        #[inline(always)]
        pub unsafe fn $shr(a: $t, b: $t) -> $t {
            a >> (b % $bits)
        }
        #[inline(always)]
        pub unsafe fn $comp(a: $t) -> $t {
            !a
        }
        #[inline(always)]
        pub unsafe fn $neg(a: $t) -> $t {
            (0 as $t).wrapping_sub(a)
        }
        #[inline(always)]
        pub unsafe fn $eq(a1: $t, a2: $t) -> u8 {
            (a1 == a2) as u8
        }
        #[inline(always)]
        pub unsafe fn $lt(a1: $t, a2: $t) -> u8 {
            (a1 < a2) as u8
        }
        #[inline(always)]
        pub unsafe fn $le(a1: $t, a2: $t) -> u8 {
            (a1 <= a2) as u8
        }
    };
}

macro_rules! impl_sync_for_lean_objs {
    ($($name:ident),* $(,)?) => {
        $(unsafe impl<const N: usize> Sync for $name<N> {})*
    };
}

// ===== REAL LIBRARY SYMBOLS =====

extern "C" {
    pub fn lean_alloc_object(sz: usize) -> *mut lean_object;
    pub fn lean_free_object(o: *mut lean_object);
    pub fn lean_dec_ref_cold(o: *mut lean_object);

    pub fn lean_internal_panic_out_of_memory() -> !;
    pub fn lean_internal_panic_rc_overflow() -> !;

    // Once-cell cold paths
    pub fn lean_obj_once_cold(
        loc: *mut *mut lean_object,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> *mut lean_object,
    ) -> *mut lean_object;
    pub fn lean_uint8_once_cold(
        loc: *mut u8,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> u8,
    ) -> u8;
    pub fn lean_uint16_once_cold(
        loc: *mut u16,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> u16,
    ) -> u16;
    pub fn lean_uint32_once_cold(
        loc: *mut u32,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> u32,
    ) -> u32;
    pub fn lean_uint64_once_cold(
        loc: *mut u64,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> u64,
    ) -> u64;
    pub fn lean_usize_once_cold(
        loc: *mut usize,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> usize,
    ) -> usize;
    pub fn lean_float32_once_cold(
        loc: *mut f32,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> f32,
    ) -> f32;
    pub fn lean_float_once_cold(
        loc: *mut f64,
        tok: *mut lean_once_cell,
        init: unsafe extern "C" fn() -> f64,
    ) -> f64;

    // Big Nat / Int
    pub fn lean_nat_big_lt(a1: *mut lean_object, a2: *mut lean_object) -> bool;
    pub fn lean_nat_big_succ(a: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_add(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_sub(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_mul(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_overflow_mul(a1: usize, a2: usize) -> *mut lean_object;
    pub fn lean_nat_big_div(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_mod(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_eq(a1: *mut lean_object, a2: *mut lean_object) -> bool;
    pub fn lean_nat_big_le(a1: *mut lean_object, a2: *mut lean_object) -> bool;
    pub fn lean_nat_big_land(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_lor(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_xor(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_nat_big_shiftr(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;

    pub fn lean_int_big_neg(a: *mut lean_object) -> *mut lean_object;
    pub fn lean_int_big_add(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_int_big_sub(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_int_big_mul(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_int_big_div(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_int_big_ediv(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_int_big_emod(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object;
    pub fn lean_int_big_eq(a1: *mut lean_object, a2: *mut lean_object) -> bool;
    pub fn lean_int_big_le(a1: *mut lean_object, a2: *mut lean_object) -> bool;
    pub fn lean_int_big_lt(a1: *mut lean_object, a2: *mut lean_object) -> bool;
    pub fn lean_int_big_nonneg(a: *mut lean_object) -> bool;

    pub fn lean_big_usize_to_nat(n: usize) -> *mut lean_object;
    pub fn lean_big_size_t_to_int(n: usize) -> *mut lean_object;
    pub fn lean_big_int_to_int(n: c_int) -> *mut lean_object;
    pub fn lean_big_int64_to_int(n: i64) -> *mut lean_object;
    pub fn lean_big_int_to_nat(a: *mut lean_object) -> *mut lean_object;

    pub fn lean_usize_of_big_nat(a: *mut lean_object) -> usize;
    pub fn lean_uint8_of_big_nat(a: *mut lean_object) -> u8;
    pub fn lean_uint32_of_big_nat(a: *mut lean_object) -> u32;
    pub fn lean_uint64_of_big_nat(a: *mut lean_object) -> u64;

    // apply
    pub fn lean_apply_m(
        obj: *mut lean_object,
        nargs: usize,
        args: *mut *mut lean_object,
    ) -> *mut lean_object;

    // Strings
    pub fn lean_mk_string_unchecked(s: *const c_char, sz: usize, len: usize) -> *mut lean_object;
    pub fn lean_mk_string(s: *const c_char) -> *mut lean_object;
    pub fn lean_cstr_to_nat(s: *const c_char) -> *mut lean_object;
    pub fn lean_string_push(s: *mut lean_object, c: u32) -> *mut lean_object;
    pub fn lean_string_append(s1: *mut lean_object, s2: *mut lean_object) -> *mut lean_object;
    pub fn lean_string_utf8_get(s: *mut lean_object, i: *mut lean_object) -> u32;
    pub fn lean_string_utf8_next(s: *mut lean_object, i: *mut lean_object) -> *mut lean_object;
    pub fn lean_string_utf8_prev(s: *mut lean_object, i: *mut lean_object) -> *mut lean_object;
    pub fn lean_string_utf8_set(
        s: *mut lean_object,
        i: *mut lean_object,
        c: u32,
    ) -> *mut lean_object;
    pub fn lean_string_utf8_extract(
        s: *mut lean_object,
        b: *mut lean_object,
        e: *mut lean_object,
    ) -> *mut lean_object;
    pub fn lean_string_hash(s: *mut lean_object) -> u64;
    pub fn lean_string_compare(s1: *mut lean_object, s2: *mut lean_object) -> u8;
    pub fn lean_string_memcmp(
        s1: *mut lean_object,
        s2: *mut lean_object,
        lstart: *mut lean_object,
        rstart: *mut lean_object,
        len: *mut lean_object,
    ) -> u8;
    pub fn lean_string_intercalate(sep: *mut lean_object, xs: *mut lean_object)
        -> *mut lean_object;
    pub fn lean_string_from_utf8_unchecked(a: *mut lean_object) -> *mut lean_object;
    pub fn lean_string_validate_utf8(a: *mut lean_object) -> u8;
    pub fn lean_string_is_valid_pos(s: *mut lean_object, i: *mut lean_object) -> u8;
    pub fn lean_string_eq_cold(s1: *mut lean_object, s2: *mut lean_object) -> bool;
    pub fn lean_string_lt(s1: *mut lean_object, s2: *mut lean_object) -> bool;
    pub fn lean_string_utf8_get_fast_cold(
        str_ptr: *const c_char,
        i: usize,
        size: usize,
        c: u8,
    ) -> u32;
    pub fn lean_string_utf8_next_fast_cold(i: usize, c: u8) -> *mut lean_object;

    // Arrays
    pub fn lean_array_push(a: *mut lean_object, v: *mut lean_object) -> *mut lean_object;
    pub fn lean_mk_array(n: *mut lean_object, v: *mut lean_object) -> *mut lean_object;
    pub fn lean_array_to_list(a: *mut lean_object) -> *mut lean_object;
    pub fn lean_array_get_panic(def_val: *mut lean_object) -> *mut lean_object;
    pub fn lean_array_set_panic(a: *mut lean_object, v: *mut lean_object) -> *mut lean_object;
    pub fn lean_copy_expand_array(a: *mut lean_object, expand: bool) -> *mut lean_object;
    pub fn lean_copy_expand_array_nonlinear(a: *mut lean_object, expand: bool) -> *mut lean_object;

    // Name
    pub fn lean_name_eq(n1: *mut lean_object, n2: *mut lean_object) -> u8;

    // Float
    pub fn lean_float_to_string(a: f64) -> *mut lean_object;

    // IO / runtime
    pub fn lean_mark_persistent(o: *mut lean_object);
    pub fn lean_io_result_show_error(r: *mut lean_object);
    pub fn lean_io_mark_end_initialization();
    pub fn lean_io_metadata(filename: *mut lean_object) -> *mut lean_object;
    pub fn lean_panic_fn(default_val: *mut lean_object, msg: *mut lean_object) -> *mut lean_object;
    pub fn lean_panic_fn_borrowed(
        default_val: *mut lean_object,
        msg: *mut lean_object,
    ) -> *mut lean_object;
    pub fn lean_setup_args(argc: c_int, argv: *mut *mut c_char) -> *mut *mut c_char;
    pub fn lean_initialize();
    pub fn lean_initialize_runtime_module();
    pub fn lean_init_task_manager();
    pub fn lean_finalize_task_manager();
    pub fn lean_run_main(
        f: unsafe extern "C" fn(c_int, *mut *mut c_char) -> *mut lean_object,
        argc: c_int,
        argv: *mut *mut c_char,
    ) -> *mut lean_object;
    pub fn lean_inc_heartbeat();

    // ST refs
    pub fn lean_st_mk_ref(v: *mut lean_object) -> *mut lean_object;
    pub fn lean_st_ref_get(r: *mut lean_object) -> *mut lean_object;
    pub fn lean_st_ref_set(r: *mut lean_object, v: *mut lean_object) -> *mut lean_object;
    pub fn lean_st_ref_take(r: *mut lean_object) -> *mut lean_object;

    // Tasks
    pub fn lean_task_pure(a: *mut lean_object) -> *mut lean_object;
    pub fn lean_task_get(t: *const lean_object) -> *mut lean_object;
    pub fn lean_task_spawn_core(
        c: *mut lean_object,
        prio: c_uint,
        keep_alive: bool,
    ) -> *mut lean_object;
    pub fn lean_task_bind_core(
        x: *mut lean_object,
        f: *mut lean_object,
        prio: c_uint,
        sync_: bool,
        keep_alive: bool,
    ) -> *mut lean_object;
    pub fn lean_task_map_core(
        f: *mut lean_object,
        t: *mut lean_object,
        prio: c_uint,
        sync_: bool,
        keep_alive: bool,
    ) -> *mut lean_object;

    // Misc
    pub fn lean_get_set_stderr(h: *mut lean_object) -> *mut lean_object;
    pub fn lean_compacted_region_free(region: usize, unit: *mut lean_object) -> *mut lean_object;
    pub fn lean_enable_initializer_execution() -> *mut lean_object;
    pub fn lean_substring_tostring(
        s: *mut lean_object,
        b: *mut lean_object,
        e: *mut lean_object,
    ) -> *mut lean_object;
    pub fn lean_byte_array_hash(a: *mut lean_object) -> u64;
}

lean_apply_fns! {
    lean_apply_1(a1);
    lean_apply_2(a1, a2);
    lean_apply_3(a1, a2, a3);
    lean_apply_4(a1, a2, a3, a4);
    lean_apply_5(a1, a2, a3, a4, a5);
    lean_apply_6(a1, a2, a3, a4, a5, a6);
    lean_apply_7(a1, a2, a3, a4, a5, a6, a7);
    lean_apply_8(a1, a2, a3, a4, a5, a6, a7, a8);
    lean_apply_9(a1, a2, a3, a4, a5, a6, a7, a8, a9);
    lean_apply_10(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
    lean_apply_11(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
    lean_apply_12(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
    lean_apply_13(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
    lean_apply_14(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
    lean_apply_15(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
    lean_apply_16(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16);
}

// ===== RUST IMPLEMENTATIONS OF STATIC INLINE FUNCTIONS =====

// --- Pointer tagging ---

#[inline(always)]
pub unsafe fn lean_box(n: usize) -> *mut lean_object {
    ((n << 1) | 1) as *mut lean_object
}

#[inline(always)]
pub unsafe fn lean_unbox(o: *mut lean_object) -> usize {
    (o as usize) >> 1
}

#[inline(always)]
pub unsafe fn lean_is_scalar(o: *const lean_object) -> u8 {
    ((o as usize) & 1) as u8
}

// --- Object tag ---

#[inline(always)]
pub unsafe fn lean_ptr_tag(o: *mut lean_object) -> c_uint {
    *(o as *const u8).add(7) as c_uint
}

#[inline(always)]
pub unsafe fn lean_obj_tag(o: *mut lean_object) -> c_uint {
    if lean_is_scalar(o as *const lean_object) != 0 {
        lean_unbox(o) as c_uint
    } else {
        lean_ptr_tag(o)
    }
}

// --- Reference counting ---

#[inline(always)]
pub unsafe fn lean_is_st(o: *mut lean_object) -> bool {
    core::ptr::read(o as *const i32) > 0
}

#[inline(always)]
pub unsafe fn lean_is_exclusive(o: *mut lean_object) -> bool {
    lean_is_st(o) && core::ptr::read(o as *const i32) == 1
}

#[inline(always)]
pub unsafe fn lean_inc_ref_n(o: *mut lean_object, n: usize) {
    let rc = core::ptr::read(o as *const i32);
    if rc > 0 {
        core::ptr::write(o as *mut i32, rc + n as i32);
    } else if rc != 0 {
        // Negative rc = multi-threaded; fetch_sub makes it more negative (higher refcount)
        AtomicI32::from_ptr(o as *mut i32).fetch_sub(n as i32, Ordering::Relaxed);
    }
}

#[inline(always)]
pub unsafe fn lean_inc_ref(o: *mut lean_object) {
    lean_inc_ref_n(o, 1);
}

#[inline(always)]
pub unsafe fn lean_inc(o: *mut lean_object) {
    if lean_is_scalar(o as *const lean_object) == 0 {
        lean_inc_ref(o);
    }
}

#[inline(always)]
pub unsafe fn lean_inc_n(o: *mut lean_object, n: usize) {
    if lean_is_scalar(o as *const lean_object) == 0 {
        lean_inc_ref_n(o, n);
    }
}

#[inline(always)]
pub unsafe fn lean_dec_ref(o: *mut lean_object) {
    let rc = core::ptr::read(o as *const i32);
    if rc > 1 {
        core::ptr::write(o as *mut i32, rc - 1);
    } else if rc != 0 {
        lean_dec_ref_cold(o);
    }
}

#[inline(always)]
pub unsafe fn lean_dec(o: *mut lean_object) {
    if lean_is_scalar(o as *const lean_object) == 0 {
        lean_dec_ref(o);
    }
}

#[inline(always)]
pub unsafe fn lean_dec_ref_known(o: *mut lean_object, n: usize) {
    if lean_is_exclusive(o) {
        for i in 0..n {
            lean_dec(lean_ctor_get(o, i as c_uint));
        }
        lean_free_object(o);
    } else {
        lean_dec_ref(o);
    }
}

#[inline(always)]
pub unsafe fn lean_del_object(o: *mut lean_object) {
    if lean_is_scalar(o as *const lean_object) == 0 {
        lean_free_object(o);
    }
}

// --- Constructor layout ---

#[inline]
unsafe fn lean_ctor_obj_cptr(o: *mut lean_object) -> *mut *mut lean_object {
    (o as *const u8).add(core::mem::size_of::<lean_object>()) as *mut *mut lean_object
}

#[inline(always)]
pub unsafe fn lean_alloc_ctor(
    tag: c_uint,
    num_objs: c_uint,
    scalar_sz: c_uint,
) -> *mut lean_object {
    let sz = core::mem::size_of::<lean_object>()
        + core::mem::size_of::<*mut lean_object>() * num_objs as usize
        + scalar_sz as usize;
    let o = lean_alloc_object(sz);
    core::ptr::write(o as *mut i32, 1i32);
    core::ptr::write((o as *mut u8).add(4) as *mut u16, sz as u16); // m_cs_sz = total allocation size
    core::ptr::write((o as *mut u8).add(6), num_objs as u8); // m_other
    core::ptr::write((o as *mut u8).add(7), tag as u8); // m_tag
    o
}

#[inline(always)]
pub unsafe fn lean_ctor_get(o: *mut lean_object, i: c_uint) -> *mut lean_object {
    *lean_ctor_obj_cptr(o).add(i as usize)
}

#[inline(always)]
pub unsafe fn lean_ctor_set(o: *mut lean_object, i: c_uint, v: *mut lean_object) {
    *lean_ctor_obj_cptr(o).add(i as usize) = v;
}

#[inline(always)]
pub unsafe fn lean_ctor_set_tag(o: *mut lean_object, tag: c_uint) {
    core::ptr::write((o as *mut u8).add(7), tag as u8);
}

#[inline(always)]
pub unsafe fn lean_ctor_release(o: *mut lean_object, i: c_uint) {
    let objs = lean_ctor_obj_cptr(o);
    lean_dec(*objs.add(i as usize));
    *objs.add(i as usize) = lean_box(0);
}

// usize uses word-index (not byte offset) — defined separately from the byte-offset macro
#[inline(always)]
pub unsafe fn lean_ctor_get_usize(o: *mut lean_object, i: c_uint) -> usize {
    *(lean_ctor_obj_cptr(o).add(i as usize) as *const usize)
}

#[inline(always)]
pub unsafe fn lean_ctor_set_usize(o: *mut lean_object, i: c_uint, v: usize) {
    *(lean_ctor_obj_cptr(o).add(i as usize) as *mut usize) = v;
}

lean_ctor_scalar_accessors! {
    lean_ctor_get_float,   lean_ctor_set_float   => f64;
    lean_ctor_get_float32, lean_ctor_set_float32 => f32;
    lean_ctor_get_uint8,   lean_ctor_set_uint8   => u8;
    lean_ctor_get_uint16,  lean_ctor_set_uint16  => u16;
    lean_ctor_get_uint32,  lean_ctor_set_uint32  => u32;
    lean_ctor_get_uint64,  lean_ctor_set_uint64  => u64;
}

// --- Boxing / unboxing ---

// u32 fits in a tagged pointer
#[inline(always)]
pub unsafe fn lean_box_uint32(v: u32) -> *mut lean_object {
    lean_box(v as usize)
}
#[inline(always)]
pub unsafe fn lean_unbox_uint32(o: *mut lean_object) -> u32 {
    lean_unbox(o) as u32
}

// u64, f64, f32 are always heap-allocated
lean_heap_boxing! {
    lean_unbox_uint64,  lean_box_uint64  => u64, lean_ctor_get_uint64,  lean_ctor_set_uint64;
    lean_unbox_float,   lean_box_float   => f64, lean_ctor_get_float,   lean_ctor_set_float;
    lean_unbox_float32, lean_box_float32 => f32, lean_ctor_get_float32, lean_ctor_set_float32;
}

// usize: tagged pointer when it fits, heap otherwise
#[inline(always)]
pub unsafe fn lean_box_usize(n: usize) -> *mut lean_object {
    if n <= LEAN_MAX_SMALL_NAT {
        lean_box(n)
    } else {
        let r = lean_alloc_ctor(0, 0, core::mem::size_of::<usize>() as c_uint);
        lean_ctor_set_usize(r, 0, n);
        r
    }
}

#[inline(always)]
pub unsafe fn lean_unbox_usize(o: *mut lean_object) -> usize {
    if lean_is_scalar(o as *const lean_object) != 0 {
        lean_unbox(o)
    } else {
        let r = lean_ctor_get_usize(o, 0);
        lean_dec(o);
        r
    }
}

// --- Closures ---
// Layout: lean_object(8) | fun_ptr(8) | arity:u16(2) | num_fixed:u16(2) | pad(4) | objs[]

const LEAN_CLOSURE_HEADER_SIZE: usize = 24;
const LEAN_CLOSURE_TAG: u8 = 245;

#[inline(always)]
pub unsafe fn lean_alloc_closure(
    fun: *mut c_void,
    arity: c_uint,
    num_fixed: c_uint,
) -> *mut lean_object {
    let sz =
        LEAN_CLOSURE_HEADER_SIZE + core::mem::size_of::<*mut lean_object>() * num_fixed as usize;
    let o = lean_alloc_object(sz) as *mut u8;
    let hdr = o as *mut lean_object;
    core::ptr::write(hdr as *mut i32, 1i32);
    core::ptr::write(o.add(4) as *mut u16, 0u16);
    core::ptr::write(o.add(6), 0u8);
    core::ptr::write(o.add(7), LEAN_CLOSURE_TAG);
    core::ptr::write(o.add(8) as *mut *mut c_void, fun);
    core::ptr::write(o.add(16) as *mut u16, arity as u16);
    core::ptr::write(o.add(18) as *mut u16, num_fixed as u16);
    hdr
}

#[inline(always)]
pub unsafe fn lean_closure_set(o: *mut lean_object, i: c_uint, a: *mut lean_object) {
    let objs = (o as *const u8).add(LEAN_CLOSURE_HEADER_SIZE) as *mut *mut lean_object;
    *objs.add(i as usize) = a;
}

// --- Arrays ---
// Layout: lean_object(8) | m_size:usize(8) | m_capacity:usize(8) | m_data[]

const LEAN_ARRAY_HEADER_SIZE: usize = 24;
const LEAN_ARRAY_TAG: u8 = 246;

#[inline]
unsafe fn lean_array_cptr_raw(o: *mut lean_object) -> *mut *mut lean_object {
    (o as *const u8).add(LEAN_ARRAY_HEADER_SIZE) as *mut *mut lean_object
}

#[inline]
pub unsafe fn lean_array_size_raw(o: *mut lean_object) -> usize {
    core::ptr::read((o as *const u8).add(8) as *const usize)
}

#[inline(always)]
pub unsafe fn lean_array_size(o: *mut lean_object) -> usize {
    lean_array_size_raw(o)
}

#[inline(always)]
pub unsafe fn lean_array_get_size(a: *mut lean_object) -> *mut lean_object {
    lean_box(lean_array_size_raw(a))
}

#[inline(always)]
pub unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut lean_object {
    let sz = LEAN_ARRAY_HEADER_SIZE + core::mem::size_of::<*mut lean_object>() * capacity;
    let o = lean_alloc_object(sz) as *mut u8;
    let hdr = o as *mut lean_object;
    core::ptr::write(hdr as *mut i32, 1i32);
    core::ptr::write(o.add(4) as *mut u16, 0u16);
    core::ptr::write(o.add(6), 0u8);
    core::ptr::write(o.add(7), LEAN_ARRAY_TAG);
    core::ptr::write(o.add(8) as *mut usize, size);
    core::ptr::write(o.add(16) as *mut usize, capacity);
    hdr
}

#[inline(always)]
pub unsafe fn lean_mk_empty_array() -> *mut lean_object {
    lean_alloc_array(0, 0)
}

#[inline(always)]
pub unsafe fn lean_mk_empty_array_with_capacity(capacity: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(capacity as *const lean_object) == 0 {
        lean_internal_panic_out_of_memory();
    }
    lean_alloc_array(0, lean_unbox(capacity))
}

#[inline]
unsafe fn lean_ensure_exclusive_array(a: *mut lean_object) -> *mut lean_object {
    if lean_is_exclusive(a) {
        a
    } else {
        lean_copy_expand_array_nonlinear(a, false)
    }
}

#[inline(always)]
pub unsafe fn lean_array_uget(a: *mut lean_object, i: usize) -> *mut lean_object {
    let r = *lean_array_cptr_raw(a).add(i);
    lean_inc(r);
    r
}

#[inline(always)]
pub unsafe fn lean_array_uget_borrowed(a: *mut lean_object, i: usize) -> *mut lean_object {
    *lean_array_cptr_raw(a).add(i)
}

#[inline(always)]
pub unsafe fn lean_array_fget(a: *mut lean_object, i: *mut lean_object) -> *mut lean_object {
    lean_array_uget(a, lean_unbox(i))
}

#[inline(always)]
pub unsafe fn lean_array_fget_borrowed(
    a: *mut lean_object,
    i: *mut lean_object,
) -> *mut lean_object {
    lean_array_uget_borrowed(a, lean_unbox(i))
}

#[inline(always)]
pub unsafe fn lean_array_get(
    def_val: *mut lean_object,
    a: *mut lean_object,
    i: *mut lean_object,
) -> *mut lean_object {
    if lean_is_scalar(i as *const lean_object) != 0 {
        let idx = lean_unbox(i);
        if idx < lean_array_size_raw(a) {
            return lean_array_uget(a, idx);
        }
    }
    lean_inc(def_val);
    lean_array_get_panic(def_val)
}

#[inline(always)]
pub unsafe fn lean_array_get_borrowed(
    def_val: *mut lean_object,
    a: *mut lean_object,
    i: *mut lean_object,
) -> *mut lean_object {
    if lean_is_scalar(i as *const lean_object) != 0 {
        let idx = lean_unbox(i);
        if idx < lean_array_size_raw(a) {
            return lean_array_uget_borrowed(a, idx);
        }
    }
    lean_inc(def_val);
    lean_array_get_panic(def_val)
}

#[inline(always)]
pub unsafe fn lean_array_uset(
    a: *mut lean_object,
    i: usize,
    v: *mut lean_object,
) -> *mut lean_object {
    let r = lean_ensure_exclusive_array(a);
    let it = lean_array_cptr_raw(r).add(i);
    lean_dec(*it);
    *it = v;
    r
}

#[inline(always)]
pub unsafe fn lean_array_fset(
    a: *mut lean_object,
    i: *mut lean_object,
    v: *mut lean_object,
) -> *mut lean_object {
    lean_array_uset(a, lean_unbox(i), v)
}

#[inline(always)]
pub unsafe fn lean_array_pop(a: *mut lean_object) -> *mut lean_object {
    let r = lean_ensure_exclusive_array(a);
    let sz = lean_array_size_raw(r);
    if sz == 0 {
        return r;
    }
    let new_sz = sz - 1;
    core::ptr::write((r as *mut u8).add(8) as *mut usize, new_sz);
    lean_dec(*lean_array_cptr_raw(r).add(new_sz));
    r
}

#[inline(always)]
pub unsafe fn lean_array_uswap(a: *mut lean_object, i: usize, j: usize) -> *mut lean_object {
    let r = lean_ensure_exclusive_array(a);
    let it = lean_array_cptr_raw(r);
    it.add(i).swap(it.add(j));
    r
}

#[inline(always)]
pub unsafe fn lean_array_fswap(
    a: *mut lean_object,
    i: *mut lean_object,
    j: *mut lean_object,
) -> *mut lean_object {
    lean_array_uswap(a, lean_unbox(i), lean_unbox(j))
}

// --- Strings ---
// Layout: lean_object(8) | m_size:usize(8) | m_capacity:usize(8) | m_length:usize(8) | data[]

#[inline]
unsafe fn lean_string_size_raw(s: *mut lean_object) -> usize {
    core::ptr::read((s as *const u8).add(8) as *const usize)
}

#[inline]
unsafe fn lean_string_len_raw(s: *mut lean_object) -> usize {
    core::ptr::read((s as *const u8).add(24) as *const usize)
}

#[inline]
unsafe fn lean_string_cstr_raw(s: *mut lean_object) -> *const c_char {
    (s as *const u8).add(32) as *const c_char
}

#[inline(always)]
pub unsafe fn lean_string_length(s: *mut lean_object) -> *mut lean_object {
    lean_box(lean_string_len_raw(s))
}

#[inline(always)]
pub unsafe fn lean_string_utf8_byte_size(s: *mut lean_object) -> *mut lean_object {
    lean_box(lean_string_size_raw(s) - 1)
}

#[inline(always)]
pub unsafe fn lean_string_dec_eq(s1: *mut lean_object, s2: *mut lean_object) -> u8 {
    (s1 == s2
        || (lean_string_size_raw(s1) == lean_string_size_raw(s2) && lean_string_eq_cold(s1, s2)))
        as u8
}

#[inline(always)]
pub unsafe fn lean_string_dec_lt(s1: *mut lean_object, s2: *mut lean_object) -> u8 {
    lean_string_lt(s1, s2) as u8
}

#[inline(always)]
pub unsafe fn lean_string_get_byte_fast(s: *mut lean_object, i: *mut lean_object) -> u8 {
    *lean_string_cstr_raw(s).add(lean_unbox(i)) as u8
}

#[inline(always)]
pub unsafe fn lean_string_utf8_get_fast(s: *mut lean_object, i: *mut lean_object) -> u32 {
    let str_ptr = lean_string_cstr_raw(s);
    let idx = lean_unbox(i);
    let c = *str_ptr.add(idx) as u8;
    if (c & 0x80) == 0 {
        c as u32
    } else {
        lean_string_utf8_get_fast_cold(str_ptr, idx, lean_string_size_raw(s), c)
    }
}

#[inline(always)]
pub unsafe fn lean_string_utf8_next_fast(
    s: *mut lean_object,
    i: *mut lean_object,
) -> *mut lean_object {
    let str_ptr = lean_string_cstr_raw(s);
    let idx = lean_unbox(i);
    let c = *str_ptr.add(idx) as u8;
    if (c & 0x80) == 0 {
        lean_box(idx + 1)
    } else {
        lean_string_utf8_next_fast_cold(idx, c)
    }
}

#[inline(always)]
pub unsafe fn lean_string_utf8_at_end(s: *mut lean_object, i: *mut lean_object) -> u8 {
    (lean_is_scalar(i as *const lean_object) == 0 || lean_unbox(i) >= lean_string_size_raw(s) - 1)
        as u8
}

// --- IO results ---

#[inline(always)]
pub unsafe fn lean_io_result_mk_ok(a: *mut lean_object) -> *mut lean_object {
    let r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, a);
    r
}

#[inline(always)]
pub unsafe fn lean_io_result_mk_error(e: *mut lean_object) -> *mut lean_object {
    let r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, e);
    r
}

#[inline(always)]
pub unsafe fn lean_io_result_is_ok(r: *mut lean_object) -> bool {
    lean_ptr_tag(r) == 0
}
#[inline(always)]
pub unsafe fn lean_io_result_is_error(r: *mut lean_object) -> bool {
    lean_ptr_tag(r) == 1
}
#[inline(always)]
pub unsafe fn lean_io_result_get_value(r: *mut lean_object) -> *mut lean_object {
    lean_ctor_get(r, 0)
}
#[inline(always)]
pub unsafe fn lean_io_result_get_error(r: *mut lean_object) -> *mut lean_object {
    lean_ctor_get(r, 0)
}

// --- Nat / Int ---

const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1;

#[inline(always)]
pub unsafe fn lean_usize_to_nat(n: usize) -> *mut lean_object {
    if n <= LEAN_MAX_SMALL_NAT {
        lean_box(n)
    } else {
        lean_big_usize_to_nat(n)
    }
}

#[inline(always)]
pub unsafe fn lean_unsigned_to_nat(n: c_uint) -> *mut lean_object {
    lean_usize_to_nat(n as usize)
}

#[inline(always)]
pub unsafe fn lean_usize_of_nat(a: *mut lean_object) -> usize {
    if lean_is_scalar(a as *const lean_object) != 0 {
        lean_unbox(a)
    } else {
        lean_usize_of_big_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_dec_lt(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        ((a1 as usize) < (a2 as usize)) as u8
    } else {
        lean_nat_big_lt(a1, a2) as u8
    }
}

#[inline(always)]
pub unsafe fn lean_nat_to_int(a: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a as *const lean_object) != 0 {
        if lean_unbox(a) <= i32::MAX as usize {
            a
        } else {
            lean_big_size_t_to_int(lean_unbox(a))
        }
    } else {
        a
    }
}

#[inline(always)]
pub unsafe fn lean_scalar_to_int(a: *mut lean_object) -> i32 {
    (lean_unbox(a) as u32) as i32
}

#[inline(always)]
pub unsafe fn lean_scalar_to_int64(a: *mut lean_object) -> i64 {
    lean_scalar_to_int(a) as i64
}

#[inline(always)]
pub unsafe fn lean_int64_to_int(n: i64) -> *mut lean_object {
    if n >= i32::MIN as i64 && n <= i32::MAX as i64 {
        lean_box(n as i32 as u32 as usize)
    } else {
        lean_big_int64_to_int(n)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_succ(a: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a as *const lean_object) != 0 {
        let v = lean_unbox(a);
        if v < LEAN_MAX_SMALL_NAT {
            lean_box(v + 1)
        } else {
            lean_big_usize_to_nat(v + 1)
        }
    } else {
        lean_nat_big_succ(a)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_add(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        let r = lean_unbox(a1).wrapping_add(lean_unbox(a2));
        if r <= LEAN_MAX_SMALL_NAT {
            lean_box(r)
        } else {
            lean_big_usize_to_nat(r)
        }
    } else {
        lean_nat_big_add(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_sub(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        let v1 = lean_unbox(a1);
        let v2 = lean_unbox(a2);
        lean_box(if v1 >= v2 { v1 - v2 } else { 0 })
    } else {
        lean_nat_big_sub(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_mul(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        let v1 = lean_unbox(a1);
        if v1 == 0 {
            return a1;
        }
        let v2 = lean_unbox(a2);
        let r = v1.wrapping_mul(v2);
        if r <= LEAN_MAX_SMALL_NAT && r / v1 == v2 {
            lean_box(r)
        } else {
            lean_nat_overflow_mul(v1, v2)
        }
    } else {
        lean_nat_big_mul(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_div(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        let v2 = lean_unbox(a2);
        lean_box(if v2 == 0 { 0 } else { lean_unbox(a1) / v2 })
    } else {
        lean_nat_big_div(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_mod(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        let v1 = lean_unbox(a1);
        let v2 = lean_unbox(a2);
        lean_box(if v2 == 0 { v1 } else { v1 % v2 })
    } else {
        lean_nat_big_mod(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_eq(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        (a1 == a2) as u8
    } else {
        lean_nat_big_eq(a1, a2) as u8
    }
}

#[inline(always)]
pub unsafe fn lean_nat_dec_eq(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    lean_nat_eq(a1, a2)
}

#[inline(always)]
pub unsafe fn lean_nat_le(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        ((a1 as usize) <= (a2 as usize)) as u8
    } else {
        lean_nat_big_le(a1, a2) as u8
    }
}

#[inline(always)]
pub unsafe fn lean_nat_dec_le(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    lean_nat_le(a1, a2)
}

#[inline(always)]
pub unsafe fn lean_nat_land(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        ((a1 as usize) & (a2 as usize)) as *mut lean_object
    } else {
        lean_nat_big_land(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_lor(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        ((a1 as usize) | (a2 as usize)) as *mut lean_object
    } else {
        lean_nat_big_lor(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_lxor(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        lean_box(lean_unbox(a1) ^ lean_unbox(a2))
    } else {
        lean_nat_big_xor(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_shiftr(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        let s2 = lean_unbox(a2);
        lean_box(if s2 < usize::BITS as usize {
            lean_unbox(a1) >> s2
        } else {
            0
        })
    } else {
        lean_nat_big_shiftr(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_int_neg(a: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a as *const lean_object) != 0 {
        lean_int64_to_int(-lean_scalar_to_int64(a))
    } else {
        lean_int_big_neg(a)
    }
}

#[inline(always)]
pub unsafe fn lean_int_add(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        lean_int64_to_int(lean_scalar_to_int64(a1) + lean_scalar_to_int64(a2))
    } else {
        lean_int_big_add(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_int_sub(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        lean_int64_to_int(lean_scalar_to_int64(a1) - lean_scalar_to_int64(a2))
    } else {
        lean_int_big_sub(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_int_mul(a1: *mut lean_object, a2: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        lean_int64_to_int(lean_scalar_to_int64(a1) * lean_scalar_to_int64(a2))
    } else {
        lean_int_big_mul(a1, a2)
    }
}

#[inline(always)]
pub unsafe fn lean_int_eq(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        (a1 == a2) as u8
    } else {
        lean_int_big_eq(a1, a2) as u8
    }
}

#[inline(always)]
pub unsafe fn lean_int_dec_eq(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    lean_int_eq(a1, a2)
}

#[inline(always)]
pub unsafe fn lean_int_lt(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        (lean_scalar_to_int64(a1) < lean_scalar_to_int64(a2)) as u8
    } else {
        lean_int_big_lt(a1, a2) as u8
    }
}

#[inline(always)]
pub unsafe fn lean_int_dec_lt(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    lean_int_lt(a1, a2)
}

#[inline(always)]
pub unsafe fn lean_int_le(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    if lean_is_scalar(a1 as *const lean_object) != 0
        && lean_is_scalar(a2 as *const lean_object) != 0
    {
        (lean_scalar_to_int64(a1) <= lean_scalar_to_int64(a2)) as u8
    } else {
        lean_int_big_le(a1, a2) as u8
    }
}

#[inline(always)]
pub unsafe fn lean_int_dec_le(a1: *mut lean_object, a2: *mut lean_object) -> u8 {
    lean_int_le(a1, a2)
}

#[inline(always)]
pub unsafe fn lean_int_dec_nonneg(a: *mut lean_object) -> u8 {
    if lean_is_scalar(a as *const lean_object) != 0 {
        (lean_scalar_to_int(a) >= 0) as u8
    } else {
        lean_int_big_nonneg(a) as u8
    }
}

#[inline(always)]
pub unsafe fn lean_int_neg_succ_of_nat(a: *mut lean_object) -> *mut lean_object {
    let s = lean_nat_succ(a);
    lean_dec(a);
    let i = lean_nat_to_int(s);
    let r = lean_int_neg(i);
    lean_dec(i);
    r
}

#[inline(always)]
pub unsafe fn lean_int_to_nat(a: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(a as *const lean_object) != 0 {
        a
    } else {
        lean_big_int_to_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_nat_abs(i: *mut lean_object) -> *mut lean_object {
    if lean_int_lt(i, lean_box(0)) != 0 {
        lean_int_to_nat(lean_int_neg(i))
    } else {
        lean_inc(i);
        lean_int_to_nat(i)
    }
}

// --- usize arithmetic ---

#[inline(always)]
pub unsafe fn lean_usize_add(a1: usize, a2: usize) -> usize {
    a1.wrapping_add(a2)
}
#[inline(always)]
pub unsafe fn lean_usize_sub(a1: usize, a2: usize) -> usize {
    a1.wrapping_sub(a2)
}
#[inline(always)]
pub unsafe fn lean_usize_land(a: usize, b: usize) -> usize {
    a & b
}
#[inline(always)]
pub unsafe fn lean_usize_lor(a: usize, b: usize) -> usize {
    a | b
}
#[inline(always)]
pub unsafe fn lean_usize_lxor(a: usize, b: usize) -> usize {
    a ^ b
}
#[inline(always)]
pub unsafe fn lean_usize_shift_left(a: usize, b: usize) -> usize {
    a << (b % usize::BITS as usize)
}
#[inline(always)]
pub unsafe fn lean_usize_shift_right(a: usize, b: usize) -> usize {
    a >> (b % usize::BITS as usize)
}
#[inline(always)]
pub unsafe fn lean_usize_dec_eq(a1: usize, a2: usize) -> u8 {
    (a1 == a2) as u8
}
#[inline(always)]
pub unsafe fn lean_usize_dec_lt(a1: usize, a2: usize) -> u8 {
    (a1 < a2) as u8
}
#[inline(always)]
pub unsafe fn lean_usize_dec_le(a1: usize, a2: usize) -> u8 {
    (a1 <= a2) as u8
}

// --- uint8 / uint32 / uint64 via macro ---

lean_uint_ops! {
    u8, 8,
    lean_uint8_of_nat, lean_uint8_of_big_nat,
    lean_uint8_add, lean_uint8_sub, lean_uint8_mul, lean_uint8_div, lean_uint8_mod,
    lean_uint8_land, lean_uint8_lor, lean_uint8_xor, lean_uint8_shift_left, lean_uint8_shift_right,
    lean_uint8_complement, lean_uint8_neg,
    lean_uint8_dec_eq, lean_uint8_dec_lt, lean_uint8_dec_le
}

lean_uint_ops! {
    u32, 32,
    lean_uint32_of_nat, lean_uint32_of_big_nat,
    lean_uint32_add, lean_uint32_sub, lean_uint32_mul, lean_uint32_div, lean_uint32_mod,
    lean_uint32_land, lean_uint32_lor, lean_uint32_xor, lean_uint32_shift_left, lean_uint32_shift_right,
    lean_uint32_complement, lean_uint32_neg,
    lean_uint32_dec_eq, lean_uint32_dec_lt, lean_uint32_dec_le
}

lean_uint_ops! {
    u64, 64,
    lean_uint64_of_nat, lean_uint64_of_big_nat,
    lean_uint64_add, lean_uint64_sub, lean_uint64_mul, lean_uint64_div, lean_uint64_mod,
    lean_uint64_land, lean_uint64_lor, lean_uint64_xor, lean_uint64_shift_left, lean_uint64_shift_right,
    lean_uint64_complement, lean_uint64_neg,
    lean_uint64_dec_eq, lean_uint64_dec_lt, lean_uint64_dec_le
}

// to_nat: defined manually for all three.
// u8/u32 always fit in usize, so lean_usize_to_nat is correct.
// u64 may exceed usize on 32-bit targets, so it needs its own range check.
#[inline(always)]
pub unsafe fn lean_uint8_to_nat(a: u8) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}
#[inline(always)]
pub unsafe fn lean_uint32_to_nat(a: u32) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}
#[inline(always)]
pub unsafe fn lean_uint64_to_nat(n: u64) -> *mut lean_object {
    if n <= LEAN_MAX_SMALL_NAT as u64 {
        lean_box(n as usize)
    } else {
        lean_big_usize_to_nat(n as usize)
    }
}

// Cross-type widening / narrowing conversions
#[inline(always)]
pub unsafe fn lean_uint8_to_uint32(a: u8) -> u32 {
    a as u32
}
#[inline(always)]
pub unsafe fn lean_uint8_to_uint64(a: u8) -> u64 {
    a as u64
}
#[inline(always)]
pub unsafe fn lean_uint8_to_usize(a: u8) -> usize {
    a as usize
}
#[inline(always)]
pub unsafe fn lean_uint32_to_uint8(a: u32) -> u8 {
    a as u8
}
#[inline(always)]
pub unsafe fn lean_uint32_to_uint64(a: u32) -> u64 {
    a as u64
}
#[inline(always)]
pub unsafe fn lean_uint32_to_usize(a: u32) -> usize {
    a as usize
}
#[inline(always)]
pub unsafe fn lean_uint64_to_uint8(a: u64) -> u8 {
    a as u8
}
#[inline(always)]
pub unsafe fn lean_uint64_to_uint32(a: u64) -> u32 {
    a as u32
}
#[inline(always)]
pub unsafe fn lean_uint64_to_usize(a: u64) -> usize {
    a as usize
}

// --- Once-cell fast paths ---

// lean_obj_once has loc: *mut *mut lean_object, which can't go through the scalar macro
#[inline(always)]
pub unsafe fn lean_obj_once(
    loc: *mut *mut lean_object,
    tok: *mut lean_once_cell,
    init: unsafe extern "C" fn() -> *mut lean_object,
) -> *mut lean_object {
    if AtomicI32::from_ptr(&raw mut (*tok).state).load(Ordering::Relaxed) == 1 {
        *loc
    } else {
        lean_obj_once_cold(loc, tok, init)
    }
}

lean_once_fns! {
    lean_uint8_once,   lean_uint8_once_cold   => u8;
    lean_uint16_once,  lean_uint16_once_cold  => u16;
    lean_uint32_once,  lean_uint32_once_cold  => u32;
    lean_uint64_once,  lean_uint64_once_cold  => u64;
    lean_usize_once,   lean_usize_once_cold   => usize;
    lean_float_once,   lean_float_once_cold   => f64;
    lean_float32_once, lean_float32_once_cold => f32;
}

// --- Float ---

#[inline(always)]
pub unsafe fn lean_float_add(a: f64, b: f64) -> f64 {
    a + b
}
#[inline(always)]
pub unsafe fn lean_float_sub(a: f64, b: f64) -> f64 {
    a - b
}
#[inline(always)]
pub unsafe fn lean_float_mul(a: f64, b: f64) -> f64 {
    a * b
}
#[inline(always)]
pub unsafe fn lean_float_div(a: f64, b: f64) -> f64 {
    a / b
}
#[inline(always)]
pub unsafe fn lean_float_negate(a: f64) -> f64 {
    -a
}
#[inline(always)]
pub unsafe fn lean_float_beq(a: f64, b: f64) -> u8 {
    (a == b) as u8
}
#[inline(always)]
pub unsafe fn lean_float_decLe(a: f64, b: f64) -> u8 {
    (a <= b) as u8
}
#[inline(always)]
pub unsafe fn lean_float_decLt(a: f64, b: f64) -> u8 {
    (a < b) as u8
}

// --- Misc ---

#[inline(always)]
pub unsafe fn lean_uint64_mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    let mut k = k.wrapping_mul(M);
    k ^= k >> 47;
    k ^= M;
    (h ^ k).wrapping_mul(M)
}

#[inline(always)]
pub unsafe fn lean_strict_and(b1: u8, b2: u8) -> u8 {
    b1 & b2
}
#[inline(always)]
pub unsafe fn lean_strict_or(b1: u8, b2: u8) -> u8 {
    b1 | b2
}
#[inline(always)]
pub unsafe fn lean_ptr_addr(a: *mut lean_object) -> usize {
    a as usize
}

#[inline(always)]
pub unsafe fn lean_hashmap_mk_idx(sz: *mut lean_object, hash: u64) -> usize {
    (hash % lean_unbox(sz) as u64) as usize
}

#[inline(always)]
pub unsafe fn lean_hashset_mk_idx(sz: *mut lean_object, hash: u64) -> usize {
    (hash % lean_unbox(sz) as u64) as usize
}

// --- Scalar arrays ---

const LEAN_SCALAR_ARRAY_TAG: u8 = 248;

#[inline(always)]
pub unsafe fn lean_alloc_sarray(
    elem_size: c_uint,
    size: usize,
    capacity: usize,
) -> *mut lean_object {
    let sz = core::mem::size_of::<lean_object>()
        + core::mem::size_of::<usize>() * 2
        + elem_size as usize * capacity;
    let o = lean_alloc_object(sz);
    core::ptr::write(o as *mut i32, 1i32);
    core::ptr::write((o as *mut u8).add(6), elem_size as u8);
    core::ptr::write((o as *mut u8).add(7), LEAN_SCALAR_ARRAY_TAG);
    let base = (o as *mut u8).add(core::mem::size_of::<lean_object>());
    core::ptr::write(base as *mut usize, size);
    core::ptr::write(
        base.add(core::mem::size_of::<usize>()) as *mut usize,
        capacity,
    );
    o
}

#[inline(always)]
pub unsafe fn lean_mk_empty_byte_array(capacity: *mut lean_object) -> *mut lean_object {
    if lean_is_scalar(capacity as *const lean_object) == 0 {
        lean_internal_panic_out_of_memory()
    }
    lean_alloc_sarray(1, 0, lean_unbox(capacity))
}

// --- Task wrappers ---

#[inline(always)]
pub unsafe fn lean_task_spawn(c: *mut lean_object, prio: *mut lean_object) -> *mut lean_object {
    lean_task_spawn_core(c, lean_unbox(prio) as c_uint, false)
}

#[inline(always)]
pub unsafe fn lean_task_bind(
    x: *mut lean_object,
    f: *mut lean_object,
    prio: *mut lean_object,
    sync_: u8,
) -> *mut lean_object {
    lean_task_bind_core(x, f, lean_unbox(prio) as c_uint, sync_ != 0, false)
}

#[inline(always)]
pub unsafe fn lean_task_map(
    f: *mut lean_object,
    t: *mut lean_object,
    prio: *mut lean_object,
    sync_: u8,
) -> *mut lean_object {
    lean_task_map_core(f, t, lean_unbox(prio) as c_uint, sync_ != 0, false)
}

#[inline(always)]
pub unsafe fn lean_task_get_own(t: *mut lean_object) -> *mut lean_object {
    let r = lean_task_get(t as *const lean_object);
    lean_inc(r);
    lean_dec(t);
    r
}

// ===== GENERIC OBJECT LAYOUT TYPES =====

#[repr(C)]
pub struct lean_ctor_object<const N: usize> {
    pub m_header: lean_object,
    pub m_objs: [*mut lean_object; N],
}

#[repr(C)]
pub struct lean_closure_object<const N: usize> {
    pub m_header: lean_object,
    pub m_fun: *const c_void,
    pub m_arity: u16,
    pub m_num_fixed: u16,
    pub m_objs: [*mut lean_object; N],
}

#[repr(C)]
pub struct lean_array_object<const N: usize> {
    pub m_header: lean_object,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_data: [*mut lean_object; N],
}

#[repr(C)]
pub struct lean_sarray_object<const N: usize> {
    pub m_header: lean_object,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_data: [u8; N],
}

#[repr(C)]
pub struct lean_string_object<const N: usize> {
    pub m_header: lean_object,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_length: usize,
    pub m_data: [u8; N],
}

impl_sync_for_lean_objs! {
    lean_ctor_object,
    lean_closure_object,
    lean_array_object,
    lean_sarray_object,
    lean_string_object,
}
