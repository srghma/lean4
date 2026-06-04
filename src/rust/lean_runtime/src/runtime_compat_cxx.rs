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
    if lean_is_exclusive(a) { a } else { array_clone(a) }
}

unsafe fn array_get_obj(a: *mut LeanObject, idx: usize, inc: bool) -> *mut LeanObject {
    let v = *array_elem_ptr(a, idx);
    if inc { lean_inc(v); }
    v
}

unsafe fn array_set_obj(a: *mut LeanObject, idx: usize, v: *mut LeanObject) -> *mut LeanObject {
    let r = array_ensure_writable(a);
    let slot = array_elem_ptr(r, idx);
    let old = *slot;
    if !old.is_null() {
        lean_dec(old);
    }
    *slot = v;
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
    (*((r as *mut u8).add(core::mem::size_of::<LeanArrayObject>()) as *mut usize)) = size - 1;
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
            if std::env::var_os("LEAN_TRACE_NAT_INT").is_some() {
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
pub unsafe extern "C" fn lean_string_length_export(s: *mut LeanObject) -> usize {
    lean_string_len(s)
}

#[export_name = "lean_string_utf8_byte_size"]
pub unsafe extern "C" fn lean_string_utf8_byte_size_export(s: *mut LeanObject) -> usize {
    lean_string_size(s).saturating_sub(1)
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
    lean_nat_big_eq(a, b) as u8
}

#[export_name = "lean_nat_dec_le"]
pub unsafe extern "C" fn lean_nat_dec_le_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> u8 {
    trace_compat!("lean_nat_dec_le");
    lean_nat_big_le(a, b) as u8
}

#[export_name = "lean_nat_dec_lt"]
pub unsafe extern "C" fn lean_nat_dec_lt_export(
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> u8 {
    trace_compat!("lean_nat_dec_lt");
    lean_nat_big_lt(a, b) as u8
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
pub unsafe extern "C" fn lean_array_get_size_export(obj: *mut LeanObject) -> Size {
    lean_array_size(obj)
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
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    array_get_obj(a, lean_unbox(i), false)
}

#[export_name = "lean_array_get"]
pub unsafe extern "C" fn lean_array_get_export(
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    array_get_obj(a, lean_unbox(i), true)
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
