/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use core::ptr::null_mut;

#[repr(C)]
struct libc_FILE {
    _opaque: [u8; 0],
}

static IO_SHIM_INIT: AtomicBool = AtomicBool::new(false);
static mut IO_SHIM_STDIN: *mut LeanObject = null_mut();
static mut IO_SHIM_STDOUT: *mut LeanObject = null_mut();
static mut IO_SHIM_STDERR: *mut LeanObject = null_mut();
static mut IO_HANDLE_EXTERNAL_CLASS: *mut LeanExternalClass = null_mut();
static DEBUG_ARRAY_SIZES: std::sync::OnceLock<std::sync::Mutex<std::collections::VecDeque<(usize, usize)>>> = std::sync::OnceLock::new();
static DEBUG_NAT_LTS: std::sync::OnceLock<std::sync::Mutex<std::collections::VecDeque<(usize, usize, u8)>>> = std::sync::OnceLock::new();
static DEBUG_ARRAY_PUSHES: std::sync::OnceLock<std::sync::Mutex<std::collections::VecDeque<(usize, usize, usize, usize, usize)>>> = std::sync::OnceLock::new();

fn debug_array_size_log(obj: *mut LeanObject, size: usize) {
    if !get_env_var_cached!("LEAN_DEBUG_ARRAY_SIZES") {
        return;
    }
    let log = DEBUG_ARRAY_SIZES.get_or_init(|| std::sync::Mutex::new(std::collections::VecDeque::with_capacity(128)));
    let Ok(mut log) = log.lock() else {
        return;
    };
    if log.len() == 128 {
        log.pop_front();
    }
    log.push_back((obj as usize, size));
}

fn debug_array_size_dump() {
    if !get_env_var_cached!("LEAN_DEBUG_ARRAY_SIZES") {
        return;
    }
    if let Some(log) = DEBUG_ARRAY_SIZES.get() {
        if let Ok(log) = log.lock() {
            eprintln!("recent lean_array_get_size calls:");
            for (idx, (obj, size)) in log.iter().enumerate() {
                eprintln!("  {idx:03}: array=0x{obj:x} size={size}");
            }
        }
    }
}

fn debug_nat_lt_log(a: usize, b: usize, result: u8) {
    if !get_env_var_cached!("LEAN_DEBUG_NAT_DEC") {
        return;
    }
    let log = DEBUG_NAT_LTS.get_or_init(|| std::sync::Mutex::new(std::collections::VecDeque::with_capacity(128)));
    let Ok(mut log) = log.lock() else {
        return;
    };
    if log.len() == 128 {
        log.pop_front();
    }
    log.push_back((a, b, result));
}

fn debug_nat_lt_dump() {
    if !get_env_var_cached!("LEAN_DEBUG_NAT_DEC") {
        return;
    }
    if let Some(log) = DEBUG_NAT_LTS.get() {
        if let Ok(log) = log.lock() {
            eprintln!("recent lean_nat_dec_lt scalar calls:");
            for (idx, (a, b, result)) in log.iter().enumerate() {
                eprintln!("  {idx:03}: {a} < {b} => {result}");
            }
        }
    }
}

fn debug_array_push_log(old: *mut LeanObject, old_size: usize, new: *mut LeanObject, new_size: usize, value: *mut LeanObject) {
    if !get_env_var_cached!("LEAN_DEBUG_ARRAY_PUSH_RING") {
        return;
    }
    let log = DEBUG_ARRAY_PUSHES.get_or_init(|| std::sync::Mutex::new(std::collections::VecDeque::with_capacity(128)));
    let Ok(mut log) = log.lock() else {
        return;
    };
    if log.len() == 128 {
        log.pop_front();
    }
    log.push_back((old as usize, old_size, new as usize, new_size, value as usize));
}

fn debug_array_push_dump() {
    if !get_env_var_cached!("LEAN_DEBUG_ARRAY_PUSH_RING") {
        return;
    }
    if let Some(log) = DEBUG_ARRAY_PUSHES.get() {
        if let Ok(log) = log.lock() {
            eprintln!("recent lean_array_push calls:");
            for (idx, (old, old_size, new, new_size, value)) in log.iter().enumerate() {
                eprintln!("  {idx:03}: old=0x{old:x} old_size={old_size} new=0x{new:x} new_size={new_size} value=0x{value:x}");
            }
        }
    }
}

unsafe extern "C" fn io_handle_noop_finalize(_: *mut c_void) {}
unsafe extern "C" fn io_handle_noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

extern "C" {
    #[link_name = "_ZN4lean5allocEm"]
    fn lean_alloc_mangled(sz: usize) -> *mut u8;
    #[link_name = "_ZN4lean7deallocEPvm"]
    fn lean_dealloc_mangled(o: *mut u8, sz: usize);
    #[link_name = "stdin"]
    static mut libc_stdin: *mut c_void;
    #[link_name = "stdout"]
    static mut libc_stdout: *mut c_void;
    #[link_name = "stderr"]
    static mut libc_stderr: *mut c_void;

    fn lean_expr_abstract_range(
        e: *mut LeanObject,
        n: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_expr_abstract(e: *mut LeanObject, subst: *mut LeanObject) -> *mut LeanObject;
    fn lean_find_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    fn lean_find_ext_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_instantiate1(a: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_instantiate(a: *mut LeanObject, subst: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_instantiate_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_expr_instantiate_rev(a: *mut LeanObject, subst: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_instantiate_rev_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_expr_eqv(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    fn lean_expr_equal(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    fn lean_expr_quick_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    fn lean_expr_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    fn lean_expr_dbg_to_string(e: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_has_loose_bvar(e: *mut LeanObject, i: *mut LeanObject) -> u8;
    fn lean_expr_lift_loose_bvars(
        e: *mut LeanObject,
        s: *mut LeanObject,
        d: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_expr_lower_loose_bvars(
        e: *mut LeanObject,
        s: *mut LeanObject,
        d: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_level_eqv(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
    fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
    fn lean_replace_expr(f: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    fn lean_instantiate_level_mvars(
        mctx: *mut LeanObject,
        l: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_instantiate_expr_mvars(
        mctx: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_report_profiling_time(category: *const c_char, seconds: f64);
    fn lean_exclude_profiling_time_from_current_task(seconds: f64);
    fn lean_has_no_block_profiling_task() -> bool;
    fn lean_profileit(
        category: *mut LeanObject,
        opts: *mut LeanObject,
        func: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject;

    fn lean_string_utf8_get(s: *mut LeanObject, i0: *mut LeanObject) -> u32;
    fn lean_string_utf8_next(s: *mut LeanObject, i0: *mut LeanObject) -> *mut LeanObject;
    fn lean_nat_big_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
    fn lean_nat_big_le(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
    fn lean_nat_big_lt(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
    fn lean_nat_big_mul(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
    fn lean_nat_big_div(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
    fn lean_nat_big_mod(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
    fn lean_nat_big_shiftr(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
    fn lean_option_get_or_block(o_opt: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_as_task(act: *mut LeanObject, prio: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_map_task(
        f: *mut LeanObject,
        t: *mut LeanObject,
        prio: *mut LeanObject,
        sync: u8,
    ) -> *mut LeanObject;
    fn lean_io_bind_task(
        t: *mut LeanObject,
        f: *mut LeanObject,
        prio: *mut LeanObject,
        sync: u8,
    ) -> *mut LeanObject;
    fn lean_io_prim_handle_mk(filename: *mut LeanObject, mode: u8) -> *mut LeanObject;
    fn lean_io_prim_handle_lock(h: *mut LeanObject, x: u8) -> *mut LeanObject;
    fn lean_io_prim_handle_try_lock(h: *mut LeanObject, x: u8) -> *mut LeanObject;
    fn lean_io_prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_realpath(filename: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_rename(from: *mut LeanObject, to: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_app_path() -> *mut LeanObject;
}

macro_rules! define_uint_dec_cmp {
    ($eq_fn:ident, $lt_fn:ident, $le_fn:ident, $ty:ty, $name:literal) => {
        #[export_name = concat!("lean_", $name, "_dec_eq")]
        pub unsafe extern "C" fn $eq_fn(a: $ty, b: $ty) -> u8 {
            trace_compat!(concat!("lean_", $name, "_dec_eq"));
            (a == b) as u8
        }

        #[export_name = concat!("lean_", $name, "_dec_lt")]
        pub unsafe extern "C" fn $lt_fn(a: $ty, b: $ty) -> u8 {
            trace_compat!(concat!("lean_", $name, "_dec_lt"));
            (a < b) as u8
        }

        #[export_name = concat!("lean_", $name, "_dec_le")]
        pub unsafe extern "C" fn $le_fn(a: $ty, b: $ty) -> u8 {
            trace_compat!(concat!("lean_", $name, "_dec_le"));
            (a <= b) as u8
        }
    };
}

macro_rules! define_uint_of_nat {
    ($of_fn:ident, $mk_fn:ident, $ty:ty, $big_fn:path, $name:literal) => {
        #[export_name = concat!("lean_", $name, "_of_nat")]
        pub unsafe extern "C" fn $of_fn(a: *mut LeanObject) -> $ty {
            trace_compat!(concat!("lean_", $name, "_of_nat"));
            if lean_is_scalar(a) {
                lean_unbox(a) as $ty
            } else {
                $big_fn(a)
            }
        }

        #[export_name = concat!("lean_", $name, "_of_nat_mk")]
        pub unsafe extern "C" fn $mk_fn(a: *mut LeanObject) -> $ty {
            trace_compat!(concat!("lean_", $name, "_of_nat_mk"));
            let r = if lean_is_scalar(a) {
                lean_unbox(a) as $ty
            } else {
                $big_fn(a)
            };
            lean_dec(a);
            r
        }
    };
}

#[inline]
unsafe fn lean_scalar_to_int64_obj(a: *mut LeanObject) -> i64 {
    #[cfg(target_pointer_width = "64")]
    {
        lean_unbox(a) as u32 as i32 as i64
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        (a as isize >> 1) as i64
    }
}

#[inline]
unsafe fn lean_scalar_to_int_obj(a: *mut LeanObject) -> i32 {
    lean_scalar_to_int64_obj(a) as i32
}

#[inline]
unsafe fn lean_int_to_nat_obj(a: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) {
        a
    } else {
        crate::runtime_object_nat_int_impl::lean_big_int_to_nat(a)
    }
}

#[inline]
unsafe fn lean_int_lt_obj(a: *mut LeanObject, b: *mut LeanObject) -> bool {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_scalar_to_int_obj(a) < lean_scalar_to_int_obj(b)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_lt(a, b)
    }
}

#[inline]
unsafe fn lean_int64_to_int_obj(v: i64) -> *mut LeanObject {
    crate::lean_int64_to_int_export(v)
}

unsafe fn array_elem_ptr(a: *mut LeanObject, idx: usize) -> *mut *mut LeanObject {
    lean_array_cptr(a).add(idx)
}

unsafe fn array_clone(a: *mut LeanObject) -> *mut LeanObject {
    let size = lean_array_size(a);
    let cap = lean_array_capacity(a);
    let r = lean_alloc_array(size, cap);
    let src = lean_array_cptr(a);
    let dst = lean_array_cptr(r);
    for i in 0..size {
        let v = *src.add(i);
        *dst.add(i) = v;
        lean_inc(v);
    }
    r
}

unsafe fn array_ensure_writable(a: *mut LeanObject) -> *mut LeanObject {
    if lean_is_exclusive(a) {
        a
    } else {
        let r = array_clone(a);
        lean_dec(a);
        r
    }
}

unsafe fn array_get_obj(a: *mut LeanObject, idx: usize, inc: bool) -> *mut LeanObject {
    let v = *array_elem_ptr(a, idx);
    if inc { lean_inc(v); }
    v
}

unsafe fn array_get_checked_obj(
    def_val: *mut LeanObject,
    a: *mut LeanObject,
    i: *mut LeanObject,
    inc_result: bool,
) -> *mut LeanObject {
    if lean_is_scalar(i) {
        let idx = lean_unbox(i);
        let size = lean_array_size(a);
        if idx < size {
            return array_get_obj(a, idx, inc_result);
        }
        if get_env_var_cached!("LEAN_DEBUG_ARRAY_GET") {
            eprintln!(
                "lean_array_get_checked_oob def={:p} array={:p} size={} idx={} caller={:p}",
                def_val,
                a,
                size,
                idx,
                std::panic::Location::caller() as *const _,
            );
            eprintln!("{}", std::backtrace::Backtrace::force_capture());
        }
        debug_array_size_dump();
        debug_nat_lt_dump();
        debug_array_push_dump();
    } else if get_env_var_cached!("LEAN_DEBUG_ARRAY_GET") {
        eprintln!(
            "lean_array_get_checked_non_scalar_index def={:p} array={:p} index={:p}",
            def_val,
            a,
            i,
        );
        eprintln!("{}", std::backtrace::Backtrace::force_capture());
    }
    lean_inc(def_val);
    crate::runtime_object_array_impl::lean_array_get_panic(def_val)
}

unsafe fn array_set_obj(a: *mut LeanObject, idx: usize, v: *mut LeanObject) -> *mut LeanObject {
    let old_size = lean_array_size(a);
    let r = array_ensure_writable(a);
    let slot = array_elem_ptr(r, idx);
    let old = *slot;
    if !old.is_null() {
        lean_dec(old);
    }
    *slot = v;
    if get_env_var_cached!("LEAN_DEBUG_ARRAY_USET") {
        let bt = std::backtrace::Backtrace::force_capture().to_string();
        if bt.contains("elabMutualDef_go_spec__1") || bt.contains("elabMutualDef_go_spec__2") || bt.contains("elabHeaders") {
            eprintln!(
                "lean_array_uset old={:p} old_size={} idx={} new={:p} new_size={} value={:p}",
                a,
                old_size,
                idx,
                r,
                lean_array_size(r),
                v,
            );
            eprintln!("{bt}");
        }
    }
    r
}

unsafe fn array_pop_obj(a: *mut LeanObject) -> *mut LeanObject {
    let size = lean_array_size(a);
    if size == 0 {
        return a;
    }
    let r = array_ensure_writable(a);
    let slot = array_elem_ptr(r, size - 1);
    let old = *slot;
    if !old.is_null() {
        lean_dec(old);
    }
    (*(r as *mut LeanArrayObject)).m_size = size - 1;
    r
}

unsafe fn array_swap_obj(a: *mut LeanObject, i: usize, j: usize) -> *mut LeanObject {
    let r = array_ensure_writable(a);
    let p = array_elem_ptr(r, i);
    let q = array_elem_ptr(r, j);
    core::ptr::swap(p, q);
    r
}

macro_rules! forward_ptr_to_ptr {
    ($name:ident, $target:path, $arg:ty) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(a: $arg) -> *mut LeanObject {
            $target(a)
        }
    };
}

macro_rules! forward_ptr2_to_ptr {
    ($name:ident, $target:path, $arg1:ty, $arg2:ty) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(a1: $arg1, a2: $arg2) -> *mut LeanObject {
            $target(a1, a2)
        }
    };
}

macro_rules! forward_ptr_to_bool {
    ($name:ident, $target:path, $arg:ty) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(a: $arg) -> bool {
            $target(a)
        }
    };
}

macro_rules! forward_ptr2_to_bool {
    ($name:ident, $target:path, $arg1:ty, $arg2:ty) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(a1: $arg1, a2: $arg2) -> bool {
            $target(a1, a2)
        }
    };
}

macro_rules! forward_ptr_to_scalar {
    ($name:ident, $target:path, $ret:ty, $arg:ty) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(a: $arg) -> $ret {
            $target(a)
        }
    };
}

macro_rules! forward_ptr2_to_scalar {
    ($name:ident, $target:path, $ret:ty, $arg1:ty, $arg2:ty) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(a1: $arg1, a2: $arg2) -> $ret {
            $target(a1, a2)
        }
    };
}

macro_rules! forward_int_to_ptr {
    ($name:ident, $target:path, $arg:ty) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(n: $arg) -> *mut LeanObject {
            $target(n)
        }
    };
}

macro_rules! trace_compat {
    ($name:expr) => {{
        #[cfg(feature = "std")]
        {
            use core::sync::atomic::{AtomicUsize, Ordering};
            use std::io::Write;
            static COUNT: AtomicUsize = AtomicUsize::new(0);
            if get_env_var_cached!("LEAN_TRACE_NAT_INT") {
                let n = COUNT.fetch_add(1, Ordering::Relaxed) + 1;
                if n <= 8 || n.is_power_of_two() {
                    if let Ok(mut f) = std::fs::OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open("/tmp/lean_nat_trace.log")
                    {
                        let _ = writeln!(f, "[compat] {} {}", $name, n);
                    }
                }
            }
        }
    }};
}

forward_ptr_to_ptr!(lean_nat_big_succ_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_succ, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_add_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_add, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_sub_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_sub, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_mul_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_mul, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_overflow_mul_cxx, crate::runtime_object_nat_int_impl::lean_nat_overflow_mul, usize, usize);
forward_ptr2_to_ptr!(lean_nat_big_div_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_div, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_div_exact_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_div_exact, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_mod_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_mod, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_bool!(lean_nat_big_eq_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_eq, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_bool!(lean_nat_big_le_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_le, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_bool!(lean_nat_big_lt_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_lt, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_land_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_land, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_lor_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_lor, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_xor_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_xor, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_shiftl_cxx, crate::runtime_object_nat_int_impl::lean_nat_shiftl, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_big_shiftr_cxx, crate::runtime_object_nat_int_impl::lean_nat_big_shiftr, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_pow_cxx, crate::runtime_object_nat_int_impl::lean_nat_pow, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_nat_gcd_cxx, crate::runtime_object_nat_int_impl::lean_nat_gcd, *mut LeanObject, *mut LeanObject);
forward_ptr_to_ptr!(lean_nat_log2_cxx, crate::runtime_object_nat_int_impl::lean_nat_log2, *mut LeanObject);
forward_ptr_to_ptr!(lean_cstr_to_nat_cxx, crate::runtime_object_nat_int_impl::lean_cstr_to_nat, *const c_char);
forward_ptr_to_ptr!(lean_big_usize_to_nat_cxx, crate::runtime_object_nat_int_impl::lean_big_usize_to_nat, usize);
forward_ptr_to_ptr!(lean_big_uint64_to_nat_cxx, crate::runtime_object_nat_int_impl::lean_big_uint64_to_nat, u64);
forward_ptr_to_scalar!(lean_mpz_hash_cxx, crate::runtime_object_nat_int_impl::lean_mpz_hash, u32, *mut LeanObject);
forward_ptr2_to_scalar!(lean_mpz_eq_cxx, crate::runtime_object_nat_int_impl::lean_mpz_eq, u8, *mut LeanObject, *mut LeanObject);
forward_ptr_to_ptr!(lean_alloc_mpz_from_mpz_cxx, crate::runtime_object_nat_int_impl::lean_alloc_mpz_from_mpz, *mut LeanObject);
forward_ptr_to_scalar!(lean_uint8_of_big_nat_cxx, crate::runtime_object_nat_int_impl::lean_uint8_of_big_nat, u8, *mut LeanObject);
forward_ptr_to_scalar!(lean_uint16_of_big_nat_cxx, crate::runtime_object_nat_int_impl::lean_uint16_of_big_nat, u16, *mut LeanObject);
forward_ptr_to_scalar!(lean_uint32_of_big_nat_cxx, crate::runtime_object_nat_int_impl::lean_uint32_of_big_nat, u32, *mut LeanObject);
forward_ptr_to_scalar!(lean_uint64_of_big_nat_cxx, crate::runtime_object_nat_int_impl::lean_uint64_of_big_nat, u64, *mut LeanObject);
forward_ptr_to_scalar!(lean_usize_of_big_nat_cxx, crate::runtime_object_nat_int_impl::lean_usize_of_big_nat, usize, *mut LeanObject);
forward_ptr_to_scalar!(lean_int8_of_big_int_cxx, crate::runtime_object_nat_int_impl::lean_int8_of_big_int, i8, *mut LeanObject);
forward_ptr_to_scalar!(lean_int16_of_big_int_cxx, crate::runtime_object_nat_int_impl::lean_int16_of_big_int, i16, *mut LeanObject);
forward_ptr_to_scalar!(lean_int32_of_big_int_cxx, crate::runtime_object_nat_int_impl::lean_int32_of_big_int, i32, *mut LeanObject);
forward_ptr_to_scalar!(lean_int64_of_big_int_cxx, crate::runtime_object_nat_int_impl::lean_int64_of_big_int, i64, *mut LeanObject);
forward_ptr_to_scalar!(lean_isize_of_big_int_cxx, crate::runtime_object_nat_int_impl::lean_isize_of_big_int, isize, *mut LeanObject);
forward_ptr_to_ptr!(lean_int_big_neg_cxx, crate::runtime_object_nat_int_impl::lean_int_big_neg, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_add_cxx, crate::runtime_object_nat_int_impl::lean_int_big_add, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_sub_cxx, crate::runtime_object_nat_int_impl::lean_int_big_sub, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_mul_cxx, crate::runtime_object_nat_int_impl::lean_int_big_mul, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_div_cxx, crate::runtime_object_nat_int_impl::lean_int_big_div, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_div_exact_cxx, crate::runtime_object_nat_int_impl::lean_int_big_div_exact, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_mod_cxx, crate::runtime_object_nat_int_impl::lean_int_big_mod, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_ediv_cxx, crate::runtime_object_nat_int_impl::lean_int_big_ediv, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_ptr!(lean_int_big_emod_cxx, crate::runtime_object_nat_int_impl::lean_int_big_emod, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_bool!(lean_int_big_eq_cxx, crate::runtime_object_nat_int_impl::lean_int_big_eq, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_bool!(lean_int_big_le_cxx, crate::runtime_object_nat_int_impl::lean_int_big_le, *mut LeanObject, *mut LeanObject);
forward_ptr2_to_bool!(lean_int_big_lt_cxx, crate::runtime_object_nat_int_impl::lean_int_big_lt, *mut LeanObject, *mut LeanObject);
forward_ptr_to_bool!(lean_int_big_nonneg_cxx, crate::runtime_object_nat_int_impl::lean_int_big_nonneg, *mut LeanObject);
forward_ptr_to_ptr!(lean_big_int_to_nat_cxx, crate::runtime_object_nat_int_impl::lean_big_int_to_nat, *mut LeanObject);
forward_ptr_to_ptr!(lean_cstr_to_int_cxx, crate::runtime_object_nat_int_impl::lean_cstr_to_int, *const c_char);
forward_int_to_ptr!(lean_big_int_to_int_cxx, crate::runtime_object_nat_int_impl::lean_big_int_to_int, c_int);
forward_int_to_ptr!(lean_big_size_t_to_int_cxx, crate::runtime_object_nat_int_impl::lean_big_size_t_to_int, usize);
forward_int_to_ptr!(lean_big_int64_to_int_cxx, crate::runtime_object_nat_int_impl::lean_big_int64_to_int, i64);
forward_ptr2_to_scalar!(lean_uint64_mix_hash_cxx, crate::runtime_object_nat_int_impl::lean_uint64_mix_hash, u64, u64, u64);

forward_ptr_to_ptr!(
    lean_thunk_get_core_impl_cxx,
    crate::runtime_object_array_impl::lean_thunk_get_core,
    *mut LeanObject
);

define_uint_of_nat!(
    lean_uint8_of_nat_export,
    lean_uint8_of_nat_mk_export,
    u8,
    crate::runtime_object_nat_int_impl::lean_uint8_of_big_nat,
    "uint8"
);
define_uint_of_nat!(
    lean_uint16_of_nat_export,
    lean_uint16_of_nat_mk_export,
    u16,
    crate::runtime_object_nat_int_impl::lean_uint16_of_big_nat,
    "uint16"
);
define_uint_of_nat!(
    lean_uint32_of_nat_export,
    lean_uint32_of_nat_mk_export,
    u32,
    crate::runtime_object_nat_int_impl::lean_uint32_of_big_nat,
    "uint32"
);

#[export_name = "lean_mk_embedded_nul_error_c"]
pub unsafe extern "C" fn lean_mk_embedded_nul_error_c_export(
    str: *mut LeanObject,
) -> *mut LeanObject {
    lean_mk_embedded_nul_error_export(str)
}

#[export_name = "lean_io_wrap_handle_c"]
pub unsafe extern "C" fn lean_io_wrap_handle_c_export(fp: *mut c_void) -> *mut LeanObject {
    if IO_HANDLE_EXTERNAL_CLASS.is_null() {
        IO_HANDLE_EXTERNAL_CLASS = lean_register_external_class(
            Some(io_handle_noop_finalize),
            Some(io_handle_noop_foreach),
        );
    }
    lean_runtime_alloc_external(IO_HANDLE_EXTERNAL_CLASS, fp)
}

#[export_name = "lean_alloc_export"]
pub unsafe extern "C" fn lean_alloc_export_plain(sz: usize) -> *mut u8 {
    lean_alloc_mangled(sz)
}

#[export_name = "lean_dealloc_export"]
pub unsafe extern "C" fn lean_dealloc_export_plain(o: *mut u8, sz: usize) {
    lean_dealloc_mangled(o, sz)
}

#[export_name = "lean_cxx_expr_abstract_range"]
pub unsafe extern "C" fn lean_cxx_expr_abstract_range_export(
    e: *mut LeanObject,
    n: *mut LeanObject,
    subst: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_abstract_range(e, n, subst)
}

#[export_name = "lean_cxx_expr_abstract"]
pub unsafe extern "C" fn lean_cxx_expr_abstract_export(
    e: *mut LeanObject,
    subst: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_abstract(e, subst)
}

#[export_name = "lean_cxx_find_expr"]
pub unsafe extern "C" fn lean_cxx_find_expr_export(
    p: *mut LeanObject,
    e: *mut LeanObject,
) -> *mut LeanObject {
    lean_find_expr(p, e)
}

#[export_name = "lean_cxx_find_ext_expr"]
pub unsafe extern "C" fn lean_cxx_find_ext_expr_export(
    p: *mut LeanObject,
    e: *mut LeanObject,
) -> *mut LeanObject {
    lean_find_ext_expr(p, e)
}

#[export_name = "lean_cxx_expr_instantiate1"]
pub unsafe extern "C" fn lean_cxx_expr_instantiate1_export(
    a: *mut LeanObject,
    e: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_instantiate1(a, e)
}

#[export_name = "lean_cxx_expr_instantiate"]
pub unsafe extern "C" fn lean_cxx_expr_instantiate_export(
    a: *mut LeanObject,
    subst: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_instantiate(a, subst)
}

#[export_name = "lean_cxx_expr_instantiate_range"]
pub unsafe extern "C" fn lean_cxx_expr_instantiate_range_export(
    a: *mut LeanObject,
    begin: *mut LeanObject,
    end: *mut LeanObject,
    subst: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_instantiate_range(a, begin, end, subst)
}

#[export_name = "lean_cxx_expr_instantiate_rev"]
pub unsafe extern "C" fn lean_cxx_expr_instantiate_rev_export(
    a: *mut LeanObject,
    subst: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_instantiate_rev(a, subst)
}

#[export_name = "lean_cxx_expr_instantiate_rev_range"]
pub unsafe extern "C" fn lean_cxx_expr_instantiate_rev_range_export(
    a: *mut LeanObject,
    begin: *mut LeanObject,
    end: *mut LeanObject,
    subst: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_instantiate_rev_range(a, begin, end, subst)
}

#[export_name = "lean_cxx_expr_eqv"]
pub unsafe extern "C" fn lean_cxx_expr_eqv_export(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    lean_expr_eqv(a, b)
}

#[export_name = "lean_cxx_expr_equal"]
pub unsafe extern "C" fn lean_cxx_expr_equal_export(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    lean_expr_equal(a, b)
}

#[export_name = "lean_cxx_expr_quick_lt"]
pub unsafe extern "C" fn lean_cxx_expr_quick_lt_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> u8 {
    lean_expr_quick_lt(a, b)
}

#[export_name = "lean_cxx_expr_lt"]
pub unsafe extern "C" fn lean_cxx_expr_lt_export(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    lean_expr_lt(a, b)
}

#[export_name = "lean_cxx_expr_dbg_to_string"]
pub unsafe extern "C" fn lean_cxx_expr_dbg_to_string_export(
    e: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_dbg_to_string(e)
}

#[export_name = "lean_cxx_expr_has_loose_bvar"]
pub unsafe extern "C" fn lean_cxx_expr_has_loose_bvar_export(
    e: *mut LeanObject,
    i: *mut LeanObject,
) -> u8 {
    lean_expr_has_loose_bvar(e, i)
}

#[export_name = "lean_cxx_expr_lift_loose_bvars"]
pub unsafe extern "C" fn lean_cxx_expr_lift_loose_bvars_export(
    e: *mut LeanObject,
    s: *mut LeanObject,
    d: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_lift_loose_bvars(e, s, d)
}

#[export_name = "lean_cxx_expr_lower_loose_bvars"]
pub unsafe extern "C" fn lean_cxx_expr_lower_loose_bvars_export(
    e: *mut LeanObject,
    s: *mut LeanObject,
    d: *mut LeanObject,
) -> *mut LeanObject {
    lean_expr_lower_loose_bvars(e, s, d)
}

#[export_name = "lean_cxx_level_eqv"]
pub unsafe extern "C" fn lean_cxx_level_eqv_export(
    l1: *mut LeanObject,
    l2: *mut LeanObject,
) -> u8 {
    lean_level_eqv(l1, l2)
}

#[export_name = "lean_cxx_level_eq"]
pub unsafe extern "C" fn lean_cxx_level_eq_export(
    l1: *mut LeanObject,
    l2: *mut LeanObject,
) -> u8 {
    lean_level_eq(l1, l2)
}

#[export_name = "lean_cxx_replace_expr"]
pub unsafe extern "C" fn lean_cxx_replace_expr_export(
    f: *mut LeanObject,
    e: *mut LeanObject,
) -> *mut LeanObject {
    lean_replace_expr(f, e)
}

#[export_name = "lean_cxx_instantiate_level_mvars"]
pub unsafe extern "C" fn lean_cxx_instantiate_level_mvars_export(
    mctx: *mut LeanObject,
    l: *mut LeanObject,
) -> *mut LeanObject {
    lean_instantiate_level_mvars(mctx, l)
}

#[export_name = "lean_cxx_instantiate_expr_mvars"]
pub unsafe extern "C" fn lean_cxx_instantiate_expr_mvars_export(
    mctx: *mut LeanObject,
    e: *mut LeanObject,
) -> *mut LeanObject {
    lean_instantiate_expr_mvars(mctx, e)
}

#[export_name = "lean_cxx_report_profiling_time"]
pub unsafe extern "C" fn lean_cxx_report_profiling_time_export(category: *const c_char, seconds: f64) {
    lean_report_profiling_time(category, seconds)
}

#[export_name = "lean_cxx_exclude_profiling_time"]
pub unsafe extern "C" fn lean_cxx_exclude_profiling_time_export(seconds: f64) {
    lean_exclude_profiling_time_from_current_task(seconds)
}

#[export_name = "lean_cxx_has_no_block_profiling_task"]
pub unsafe extern "C" fn lean_cxx_has_no_block_profiling_task_export() -> bool {
    lean_has_no_block_profiling_task()
}

#[export_name = "lean_cxx_profileit"]
pub unsafe extern "C" fn lean_cxx_profileit_export(
    category: *mut LeanObject,
    opts: *mut LeanObject,
    func: *mut LeanObject,
    decl: *mut LeanObject,
) -> *mut LeanObject {
    lean_profileit(category, opts, func, decl)
}

#[export_name = "lean_string_length"]
pub unsafe extern "C" fn lean_string_length_export(s: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_string_len(s))
}

#[export_name = "lean_string_utf8_byte_size"]
pub unsafe extern "C" fn lean_string_utf8_byte_size_export(s: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_string_size(s).saturating_sub(1))
}

#[export_name = "lean_string_dec_eq"]
pub unsafe extern "C" fn lean_string_dec_eq_export(
    s1: *mut LeanObject,
    s2: *mut LeanObject,
) -> u8 {
    let eq = lean_string_size(s1) == lean_string_size(s2)
        && core::slice::from_raw_parts(lean_string_cstr(s1) as *const u8, lean_string_size(s1))
            == core::slice::from_raw_parts(lean_string_cstr(s2) as *const u8, lean_string_size(s2));
    eq as u8
}

define_uint_dec_cmp!(lean_uint8_dec_eq_export, lean_uint8_dec_lt_export, lean_uint8_dec_le_export, u8, "uint8");
define_uint_dec_cmp!(lean_uint16_dec_eq_export, lean_uint16_dec_lt_export, lean_uint16_dec_le_export, u16, "uint16");
define_uint_dec_cmp!(lean_uint32_dec_eq_export, lean_uint32_dec_lt_export, lean_uint32_dec_le_export, u32, "uint32");
define_uint_dec_cmp!(lean_uint64_dec_eq_export, lean_uint64_dec_lt_export, lean_uint64_dec_le_export, u64, "uint64");

#[export_name = "lean_nat_dec_eq"]
pub unsafe extern "C" fn lean_nat_dec_eq_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> u8 {
    trace_compat!("lean_nat_dec_eq");
    if lean_is_scalar(a) && lean_is_scalar(b) {
        (a == b) as u8
    } else {
        lean_nat_big_eq(a, b) as u8
    }
}

#[export_name = "lean_nat_dec_le"]
pub unsafe extern "C" fn lean_nat_dec_le_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> u8 {
    trace_compat!("lean_nat_dec_le");
    if lean_is_scalar(a) && lean_is_scalar(b) {
        (lean_unbox(a) <= lean_unbox(b)) as u8
    } else {
        lean_nat_big_le(a, b) as u8
    }
}

#[export_name = "lean_nat_dec_lt"]
pub unsafe extern "C" fn lean_nat_dec_lt_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> u8 {
    trace_compat!("lean_nat_dec_lt");
    let result = if lean_is_scalar(a) && lean_is_scalar(b) {
        let a = lean_unbox(a);
        let b = lean_unbox(b);
        let result = (a < b) as u8;
        debug_nat_lt_log(a, b, result);
        result
    } else {
        lean_nat_big_lt(a, b) as u8
    };
    result
}

#[export_name = "lean_nat_mul"]
pub unsafe extern "C" fn lean_nat_mul_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> *mut LeanObject {
    lean_nat_big_mul(a, b)
}

#[export_name = "lean_nat_div"]
pub unsafe extern "C" fn lean_nat_div_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> *mut LeanObject {
    lean_nat_big_div(a, b)
}

#[export_name = "lean_nat_mod"]
pub unsafe extern "C" fn lean_nat_mod_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> *mut LeanObject {
    lean_nat_big_mod(a, b)
}

#[export_name = "lean_nat_shiftr"]
pub unsafe extern "C" fn lean_nat_shiftr_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> *mut LeanObject {
    lean_nat_big_shiftr(a, b)
}

#[export_name = "lean_nat_to_int"]
pub unsafe extern "C" fn lean_nat_to_int_export(a: *mut LeanObject) -> *mut LeanObject {
    trace_compat!("lean_nat_to_int");
    if lean_is_scalar(a) {
        let v = lean_unbox(a);
        if v <= (usize::MAX >> 1) {
            a
        } else {
            crate::runtime_object_nat_int_impl::lean_big_size_t_to_int(v)
        }
    } else {
        a
    }
}

#[export_name = "lean_nat_abs"]
pub unsafe extern "C" fn lean_nat_abs_export(i: *mut LeanObject) -> *mut LeanObject {
    trace_compat!("lean_nat_abs");
    if lean_int_lt_obj(i, lean_box(0)) {
        let neg = lean_int_neg_export(i);
        let r = lean_int_to_nat_obj(neg);
        r
    } else {
        lean_inc(i);
        lean_int_to_nat_obj(i)
    }
}

#[export_name = "lean_int_neg"]
pub unsafe extern "C" fn lean_int_neg_export(a: *mut LeanObject) -> *mut LeanObject {
    trace_compat!("lean_int_neg");
    if lean_is_scalar(a) {
        lean_int64_to_int_obj(-lean_scalar_to_int64_obj(a))
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_neg(a)
    }
}

#[export_name = "lean_int_neg_succ_of_nat"]
pub unsafe extern "C" fn lean_int_neg_succ_of_nat_export(a: *mut LeanObject) -> *mut LeanObject {
    trace_compat!("lean_int_neg_succ_of_nat");
    let s = crate::lean_nat_add_export(a, lean_box(1));
    lean_dec(a);
    let i = lean_nat_to_int_export(s);
    let r = lean_int_neg_export(i);
    lean_dec(i);
    r
}

#[export_name = "lean_int_add"]
pub unsafe extern "C" fn lean_int_add_export(
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    trace_compat!("lean_int_add");
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        lean_int64_to_int_obj(lean_scalar_to_int64_obj(a1) + lean_scalar_to_int64_obj(a2))
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_add(a1, a2)
    }
}

#[export_name = "lean_string_utf8_get_fast"]
pub unsafe extern "C" fn lean_string_utf8_get_fast_export(
    s: *mut LeanObject,
    p: *mut LeanObject,
) -> u32 {
    lean_string_utf8_get(s, p)
}

#[export_name = "lean_string_utf8_next_fast"]
pub unsafe extern "C" fn lean_string_utf8_next_fast_export(
    s: *mut LeanObject,
    p: *mut LeanObject,
) -> *mut LeanObject {
    lean_string_utf8_next(s, p)
}

#[export_name = "lean_array_get_size"]
pub unsafe extern "C" fn lean_array_get_size_export(obj: *mut LeanObject) -> *mut LeanObject {
    let size = lean_array_size(obj);
    debug_array_size_log(obj, size);
    if get_env_var_cached!("LEAN_DEBUG_ARRAY_GET_SIZE_STACK") {
        let bt = std::backtrace::Backtrace::force_capture().to_string();
        if bt.contains("elabHeaders") {
            eprintln!("lean_array_get_size obj={:p} size={}", obj, size);
            eprintln!("{bt}");
        }
    }
    lean_box(size)
}

#[export_name = "lean_array_fget_borrowed"]
pub unsafe extern "C" fn lean_array_fget_borrowed_export(
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    array_get_obj(a, lean_unbox(i), false)
}

#[export_name = "lean_array_fget"]
pub unsafe extern "C" fn lean_array_fget_export(
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    array_get_obj(a, lean_unbox(i), true)
}

#[export_name = "lean_array_get_borrowed"]
pub unsafe extern "C" fn lean_array_get_borrowed_export(
    def_val: *mut LeanObject,
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    array_get_checked_obj(def_val, a, i, false)
}

#[export_name = "lean_array_get"]
pub unsafe extern "C" fn lean_array_get_export(
    def_val: *mut LeanObject,
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    array_get_checked_obj(def_val, a, i, true)
}

#[export_name = "lean_array_uget"]
pub unsafe extern "C" fn lean_array_uget_export(
    a: *mut LeanObject,
    i: usize,
) -> *mut LeanObject {
    array_get_obj(a, i, true)
}

#[export_name = "lean_array_uget_borrowed"]
pub unsafe extern "C" fn lean_array_uget_borrowed_export(
    a: *mut LeanObject,
    i: usize,
) -> *mut LeanObject {
    array_get_obj(a, i, false)
}

#[export_name = "lean_array_uset"]
pub unsafe extern "C" fn lean_array_uset_export(
    a: *mut LeanObject,
    i: usize,
    v: *mut LeanObject,
) -> *mut LeanObject {
    array_set_obj(a, i, v)
}

#[export_name = "lean_array_fset"]
pub unsafe extern "C" fn lean_array_fset_export(
    a: *mut LeanObject,
    i: *mut LeanObject,
    v: *mut LeanObject,
) -> *mut LeanObject {
    array_set_obj(a, lean_unbox(i), v)
}

#[export_name = "lean_array_set"]
pub unsafe extern "C" fn lean_array_set_export(
    a: *mut LeanObject,
    i: *mut LeanObject,
    v: *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < lean_array_size(a) {
            return array_set_obj(a, idx, v);
        }
    }
    crate::runtime_object_array_impl::lean_array_set_panic(a, v)
}

#[export_name = "lean_array_pop"]
pub unsafe extern "C" fn lean_array_pop_export(a: *mut LeanObject) -> *mut LeanObject {
    array_pop_obj(a)
}

#[export_name = "lean_array_fswap"]
pub unsafe extern "C" fn lean_array_fswap_export(
    a: *mut LeanObject,
    i: *mut LeanObject,
    j: *mut LeanObject,
) -> *mut LeanObject {
    array_swap_obj(a, lean_unbox(i), lean_unbox(j))
}

#[export_name = "lean_array_swap"]
pub unsafe extern "C" fn lean_array_swap_export(
    a: *mut LeanObject,
    i: *mut LeanObject,
    j: *mut LeanObject,
) -> *mut LeanObject {
    if !lean_is_scalar(i) || !lean_is_scalar(j) {
        return a;
    }
    let ui = lean_unbox(i);
    let uj = lean_unbox(j);
    if ui >= lean_array_size(a) || uj >= lean_array_size(a) {
        return a;
    }
    array_swap_obj(a, ui, uj)
}

#[export_name = "lean_uint8_to_nat"]
pub unsafe extern "C" fn lean_uint8_to_nat_export(n: u8) -> *mut LeanObject {
    lean_box(n as usize)
}

#[export_name = "lean_uint16_to_nat"]
pub unsafe extern "C" fn lean_uint16_to_nat_export(n: u16) -> *mut LeanObject {
    lean_box(n as usize)
}

#[export_name = "lean_uint32_to_nat"]
pub unsafe extern "C" fn lean_uint32_to_nat_export(n: u32) -> *mut LeanObject {
    lean_box(n as usize)
}

#[export_name = "lean_uint8_to_uint64"]
pub unsafe extern "C" fn lean_uint8_to_uint64_export(n: u8) -> u64 {
    n as u64
}

#[export_name = "lean_uint16_to_uint64"]
pub unsafe extern "C" fn lean_uint16_to_uint64_export(n: u16) -> u64 {
    n as u64
}

#[export_name = "lean_uint32_to_uint64"]
pub unsafe extern "C" fn lean_uint32_to_uint64_export(n: u32) -> u64 {
    n as u64
}

#[export_name = "lean_uint64_of_nat"]
pub unsafe extern "C" fn lean_uint64_of_nat_export(n: *mut LeanObject) -> u64 {
    trace_compat!("lean_uint64_of_nat");
    lean_uint64_of_nat_rust(n)
}

#[export_name = "lean_uint64_of_nat_mk"]
pub unsafe extern "C" fn lean_uint64_of_nat_mk_export(n: *mut LeanObject) -> u64 {
    trace_compat!("lean_uint64_of_nat_mk");
    let r = lean_uint64_of_nat_rust(n);
    lean_dec(n);
    r
}

#[export_name = "lean_uint64_to_nat"]
pub unsafe extern "C" fn lean_uint64_to_nat_export(n: u64) -> *mut LeanObject {
    trace_compat!("lean_uint64_to_nat");
    lean_uint64_to_nat_rust(n)
}

#[export_name = "lean_uint64_to_usize"]
pub unsafe extern "C" fn lean_uint64_to_usize_export(n: u64) -> usize {
    n as usize
}

#[export_name = "lean_uint64_lor"]
pub unsafe extern "C" fn lean_uint64_lor_export(a: u64, b: u64) -> u64 {
    a | b
}

#[export_name = "lean_uint64_xor"]
pub unsafe extern "C" fn lean_uint64_xor_export(a: u64, b: u64) -> u64 {
    a ^ b
}

#[export_name = "lean_uint64_shift_left"]
pub unsafe extern "C" fn lean_uint64_shift_left_export(a: u64, b: u64) -> u64 {
    a.wrapping_shl((b & 63) as u32)
}

#[export_name = "lean_uint64_shift_right"]
pub unsafe extern "C" fn lean_uint64_shift_right_export(a: u64, b: u64) -> u64 {
    a.wrapping_shr((b & 63) as u32)
}

#[export_name = "lean_usize_of_nat"]
pub unsafe extern "C" fn lean_usize_of_nat_export(n: *mut LeanObject) -> usize {
    trace_compat!("lean_usize_of_nat");
    lean_uint64_of_nat_rust(n) as usize
}

#[export_name = "lean_usize_of_nat_mk"]
pub unsafe extern "C" fn lean_usize_of_nat_mk_export(n: *mut LeanObject) -> usize {
    trace_compat!("lean_usize_of_nat_mk");
    let r = lean_uint64_of_nat_rust(n) as usize;
    lean_dec(n);
    r
}

#[export_name = "lean_usize_dec_eq"]
pub unsafe extern "C" fn lean_usize_dec_eq_export(a: usize, b: usize) -> u8 {
    (a == b) as u8
}

#[export_name = "lean_usize_dec_lt"]
pub unsafe extern "C" fn lean_usize_dec_lt_export(a: usize, b: usize) -> u8 {
    (a < b) as u8
}

#[export_name = "lean_usize_dec_le"]
pub unsafe extern "C" fn lean_usize_dec_le_export(a: usize, b: usize) -> u8 {
    (a <= b) as u8
}

#[export_name = "lean_usize_add"]
pub unsafe extern "C" fn lean_usize_add_export(a: usize, b: usize) -> usize {
    a.wrapping_add(b)
}

#[export_name = "lean_usize_sub"]
pub unsafe extern "C" fn lean_usize_sub_export(a: usize, b: usize) -> usize {
    a.wrapping_sub(b)
}

#[export_name = "lean_usize_land"]
pub unsafe extern "C" fn lean_usize_land_export(a: usize, b: usize) -> usize {
    a & b
}

#[export_name = "lean_mk_empty_array_with_capacity"]
pub unsafe extern "C" fn lean_mk_empty_array_with_capacity_export(c: *mut LeanObject) -> *mut LeanObject {
    lean_alloc_array(0, lean_unbox(c))
}

#[export_name = "lean_alloc_sarray_would_overflow_c"]
pub unsafe extern "C" fn lean_alloc_sarray_would_overflow_c_export(elem_size: usize, size: usize) -> bool {
    elem_size != 0 && size > usize::MAX / elem_size
}

#[export_name = "lean_errno"]
pub unsafe extern "C" fn lean_errno_export() -> c_int {
    #[cfg(any(target_os = "linux", target_os = "android"))]
    {
        *libc::__errno_location()
    }
    #[cfg(target_os = "macos")]
    {
        *libc::__error()
    }
}

#[export_name = "lean_io_as_task_core"]
pub unsafe extern "C" fn lean_io_as_task_core_export(
    act: *mut LeanObject,
    prio: usize,
) -> *mut LeanObject {
    lean_io_as_task(act, lean_box(prio))
}

#[export_name = "lean_io_map_task_core"]
pub unsafe extern "C" fn lean_io_map_task_core_export(
    f: *mut LeanObject,
    t: *mut LeanObject,
    prio: usize,
    sync: u8,
) -> *mut LeanObject {
    lean_io_map_task(f, t, lean_box(prio), sync)
}

#[export_name = "lean_io_bind_task_core"]
pub unsafe extern "C" fn lean_io_bind_task_core_export(
    t: *mut LeanObject,
    f: *mut LeanObject,
    prio: usize,
    sync: u8,
) -> *mut LeanObject {
    lean_io_bind_task(t, f, lean_box(prio), sync)
}

#[export_name = "lean_io_get_handle_c"]
pub unsafe extern "C" fn lean_io_get_handle_c_export(hfile: *mut LeanObject) -> *mut c_void {
    lean_runtime_get_external_data(hfile)
}

#[export_name = "lean_io_option_get_or_block_c"]
pub unsafe extern "C" fn lean_io_option_get_or_block_c_export(o_opt: *mut LeanObject) -> *mut LeanObject {
    lean_option_get_or_block(o_opt)
}

#[export_name = "lean_decode_io_error_c"]
pub unsafe extern "C" fn lean_decode_io_error_c_export(
    errnum: c_int,
    fname: *mut LeanObject,
) -> *mut LeanObject {
    crate::runtime_io_impl::lean_decode_io_error(errnum, fname)
}

#[export_name = "lean_decode_uv_error_c"]
pub unsafe extern "C" fn lean_decode_uv_error_c_export(
    errnum: c_int,
    fname: *mut LeanObject,
) -> *mut LeanObject {
    crate::runtime_io_impl::lean_decode_uv_error(errnum, fname)
}

#[cfg(test)]
mod runtime_compat_cxx_tests {
    use super::*;
    use core::ffi::c_uint;

    #[test]
    fn shared_array_uset_consumes_input_reference() {
        unsafe {
            let value = lean_alloc_ctor(0, 0, 0);
            let replacement = lean_box(2);
            let array = lean_alloc_array(1, 1);
            *lean_array_cptr(array) = value;
            lean_inc(array);

            let updated = lean_array_uset_export(array, 0, replacement);

            assert_ne!(updated, array);
            assert_eq!((*array).m_rc, 1);
            assert_eq!((*value).m_rc, 1);
            assert_eq!(lean_unbox(*lean_array_cptr(updated)), 2);

            lean_dec(updated);
            lean_dec(array);
        }
    }

    #[test]
    fn ctor_layout_handles_many_fields_and_odd_scalar_tail() {
        unsafe {
            let fields = 8usize;
            let scalar_size = 11usize;
            let obj = lean_alloc_ctor(0, fields as c_uint, scalar_size as c_uint);

            for i in 0..fields {
                lean_ctor_set(obj, i, lean_box(100 + i));
            }
            for i in 0..scalar_size {
                lean_ctor_set_uint8(obj, fields * core::mem::size_of::<*mut LeanObject>() + i, (17 + i) as u8);
            }

            for i in 0..fields {
                assert_eq!(lean_unbox(lean_ctor_get(obj, i)), 100 + i);
            }
            for i in 0..scalar_size {
                assert_eq!(
                    lean_ctor_get_uint8(obj, fields * core::mem::size_of::<*mut LeanObject>() + i),
                    (17 + i) as u8,
                );
            }
            assert_eq!(
                lean_object_byte_size(obj),
                (core::mem::size_of::<LeanObject>() + fields * core::mem::size_of::<*mut LeanObject>() + scalar_size + 7) & !7,
            );

            lean_dec(obj);
        }
    }
}
