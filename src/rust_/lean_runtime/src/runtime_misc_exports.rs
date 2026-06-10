#![allow(non_camel_case_types, non_snake_case)]

use crate::LeanObject;
use std::ffi::{c_void, CStr, CString};

type b_lean_obj_arg = *mut LeanObject;
type lean_obj_arg = *mut LeanObject;
type lean_obj_res = *mut LeanObject;
#[allow(dead_code)]
type b_lean_obj_res = *mut LeanObject;

const LEAN_MAX_CTOR_TAG: u8 = 243;
const LEAN_THUNK_TAG: u8 = 251;
const LEAN_EXTERNAL_TAG: u8 = 254;

#[cfg(unix)]
unsafe fn lookup_current_process_symbol(name: &CStr) -> *mut c_void {
    libc::dlsym(libc::RTLD_DEFAULT, name.as_ptr())
}

#[cfg(not(unix))]
unsafe fn lookup_current_process_symbol(_name: &CStr) -> *mut c_void {
    core::ptr::null_mut()
}

unsafe fn mk_except_ok(value: lean_obj_arg) -> lean_obj_res {
    let obj = crate::lean_alloc_ctor(1, 1, 0);
    crate::lean_ctor_set(obj, 0, value);
    obj
}

unsafe fn mk_except_error(message: &str) -> lean_obj_res {
    let cstr = CString::new(message).unwrap_or_else(|_| CString::new("evaluation failed").unwrap());
    let msg = crate::lean_mk_string(cstr.as_ptr());
    let obj = crate::lean_alloc_ctor(0, 1, 0);
    crate::lean_ctor_set(obj, 0, msg);
    obj
}

fn push_hex(out: &mut String, width: usize, value: u32) {
    for i in (0..width).rev() {
        let digit = ((value >> (4 * i)) & 0xf) as u8;
        out.push(if digit < 10 { (b'0' + digit) as char } else { (b'a' + digit - 10) as char });
    }
}

fn mangle_string_component(input: &str) -> String {
    let mut out = String::new();
    for ch in input.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else if ch == '_' {
            out.push_str("__");
        } else {
            let value = ch as u32;
            if value < 0x100 {
                out.push_str("_x");
                push_hex(&mut out, 2, value);
            } else if value < 0x10000 {
                out.push_str("_u");
                push_hex(&mut out, 4, value);
            } else {
                out.push_str("_U");
                push_hex(&mut out, 8, value);
            }
        }
    }
    out
}

fn check_lower_hex(s: &str, start: usize, count: usize) -> bool {
    s.as_bytes()
        .get(start..start.saturating_add(count))
        .is_some_and(|bytes| bytes.len() == count && bytes.iter().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b)))
}

fn check_disambiguation(s: &str) -> bool {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return true;
    }
    match bytes[0] {
        b'_' => check_disambiguation(&s[1..]),
        b'x' => check_lower_hex(s, 1, 2),
        b'u' => check_lower_hex(s, 1, 4),
        b'U' => check_lower_hex(s, 1, 8),
        b'0'..=b'9' => true,
        _ => false,
    }
}

fn need_disambiguation(prev: &LeanNamePart, next: &str) -> bool {
    matches!(prev, LeanNamePart::Str(s) if s.ends_with('_')) || check_disambiguation(next)
}

enum LeanNamePart {
    Str(String),
    Num(usize),
}

unsafe fn collect_name_parts(mut name: lean_obj_arg) -> Vec<LeanNamePart> {
    let mut rev = Vec::new();
    while !crate::lean_is_scalar(name) {
        match crate::lean_ptr_tag(name) {
            1 => {
                let s = crate::lean_ctor_get_export(name, 1);
                let text = CStr::from_ptr(crate::lean_string_cstr(s)).to_string_lossy().into_owned();
                rev.push(LeanNamePart::Str(text));
                name = crate::lean_ctor_get_export(name, 0);
            }
            2 => {
                let n = crate::lean_ctor_get_export(name, 1);
                rev.push(LeanNamePart::Num(crate::lean_unbox(n)));
                name = crate::lean_ctor_get_export(name, 0);
            }
            _ => break,
        }
    }
    rev.reverse();
    rev
}

unsafe fn mangle_name(name: lean_obj_arg, prefix: &str) -> Option<String> {
    let parts = collect_name_parts(name);
    if parts.is_empty() {
        return None;
    }
    let mut out = String::from(prefix);
    let mut prev: Option<LeanNamePart> = None;
    for part in parts {
        match &part {
            LeanNamePart::Str(s) => {
                let m = mangle_string_component(s);
                if let Some(prev_part) = &prev {
                    out.push_str(if need_disambiguation(prev_part, &m) { "_00" } else { "_" });
                } else if check_disambiguation(&m) {
                    out.push_str("00");
                }
                out.push_str(&m);
            }
            LeanNamePart::Num(n) => {
                if prev.is_some() {
                    out.push('_');
                }
                out.push_str(&n.to_string());
                out.push('_');
            }
        }
        prev = Some(part);
    }
    Some(out)
}

fn is_canonical_pointer(addr: usize) -> bool {
    #[cfg(target_pointer_width = "64")]
    {
        let hi = addr >> 47;
        hi == 0 || hi == 0x1ffff
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        addr != 0
    }
}

unsafe fn read_native_constant_or_call(addr: *mut c_void) -> lean_obj_res {
    let cell_value = *(addr as *mut *mut LeanObject);
    let cell_addr = cell_value as usize;
    if !cell_value.is_null()
        && !crate::lean_is_scalar(cell_value)
        && cell_addr % core::mem::align_of::<LeanObject>() == 0
        && is_canonical_pointer(cell_addr)
    {
        crate::lean_inc(cell_value);
        return cell_value;
    }

    let f: unsafe extern "C" fn() -> lean_obj_res = core::mem::transmute(addr);
    f()
}

type EnvironmentFindFn = unsafe extern "C" fn(b_lean_obj_arg, b_lean_obj_arg, u8) -> lean_obj_res;
type ConstantInfoTypeFn = unsafe extern "C" fn(b_lean_obj_arg) -> lean_obj_res;
type ConstantInfoValueFn = unsafe extern "C" fn(b_lean_obj_arg, u8) -> lean_obj_res;

unsafe fn lookup_runtime_fn<T>(symbol: &'static CStr) -> Option<T> {
    let addr = lookup_current_process_symbol(symbol);
    if addr.is_null() {
        None
    } else {
        Some(core::mem::transmute_copy(&addr))
    }
}

unsafe fn find_constant_info(env: b_lean_obj_arg, const_name: b_lean_obj_arg) -> Option<lean_obj_res> {
    let find: EnvironmentFindFn = lookup_runtime_fn(c"l_Lean_Environment_find_x3f")?;
    crate::lean_inc_ref(env);
    crate::lean_inc(const_name);
    let info_opt = find(env, const_name, 0);
    if crate::lean_is_scalar(info_opt) || crate::lean_ptr_tag(info_opt) == 0 {
        crate::lean_dec(info_opt);
        return None;
    }
    let info = crate::lean_ctor_get_export(info_opt, 0);
    crate::lean_inc(info);
    crate::lean_dec(info_opt);
    Some(info)
}

unsafe fn expr_const_head(mut expr: b_lean_obj_arg) -> Option<b_lean_obj_arg> {
    while !crate::lean_is_scalar(expr) && crate::lean_ptr_tag(expr) == 5 {
        expr = crate::lean_ctor_get_export(expr, 0);
    }
    if !crate::lean_is_scalar(expr) && crate::lean_ptr_tag(expr) == 4 {
        Some(crate::lean_ctor_get_export(expr, 0))
    } else {
        None
    }
}

unsafe fn runtime_extra_arity_from_result_type(ty: b_lean_obj_arg) -> u32 {
    let Some(head) = expr_const_head(ty) else {
        return 0;
    };
    match mangle_name(head, "") {
        Some(name) if name == "MacroM" || name == "Lean_MacroM" => 2,
        _ => 0,
    }
}

unsafe fn runtime_arity_from_type(env: b_lean_obj_arg, mut ty: lean_obj_res, depth: u8) -> Option<u32> {
    let mut arity = 0u32;
    while !crate::lean_is_scalar(ty) && crate::lean_ptr_tag(ty) == 7 {
        arity = arity.saturating_add(1);
        let body = crate::lean_ctor_get_export(ty, 2);
        crate::lean_inc(body);
        crate::lean_dec(ty);
        ty = body;
    }
    if arity == 0 && depth < 8 {
        if let Some(type_name) = expr_const_head(ty) {
            let info_value: ConstantInfoValueFn = lookup_runtime_fn(c"l_Lean_ConstantInfo_value_x3f")?;
            if let Some(info) = find_constant_info(env, type_name) {
                let value_opt = info_value(info, 1);
                if !crate::lean_is_scalar(value_opt) && crate::lean_ptr_tag(value_opt) != 0 {
                    let value = crate::lean_ctor_get_export(value_opt, 0);
                    crate::lean_inc(value);
                    crate::lean_dec(value_opt);
                    crate::lean_dec(ty);
                    return runtime_arity_from_type(env, value, depth + 1);
                }
                crate::lean_dec(value_opt);
            }
        }
    }
    let extra = runtime_extra_arity_from_result_type(ty);
    crate::lean_dec(ty);
    Some(arity.saturating_add(extra))
}

unsafe fn native_constant_arity(env: b_lean_obj_arg, const_name: b_lean_obj_arg) -> Option<u32> {
    let info_type: ConstantInfoTypeFn = lookup_runtime_fn(c"l_Lean_ConstantInfo_type")?;
    let info = find_constant_info(env, const_name)?;
    let ty = info_type(info);
    crate::lean_dec(info);
    runtime_arity_from_type(env, ty, 0)
}

// Get the IR arity (number of native parameters) for a constant via lean_ir_find_env_decl.
// This gives the real native arity (e.g. 1 for IO Unit functions), unlike
// native_constant_arity which computes from the Lean TYPE and gives wrong results for IO.
type IrFindEnvDeclFn = unsafe extern "C" fn(b_lean_obj_arg, b_lean_obj_arg) -> lean_obj_res;

unsafe fn ir_decl_arity(env: b_lean_obj_arg, const_name: b_lean_obj_arg) -> Option<u32> {
    let find_fn: IrFindEnvDeclFn = lookup_runtime_fn(c"lean_ir_find_env_decl")?;
    // lean_ir_find_env_decl consumes its arguments (standard Lean @[export] convention)
    crate::lean_inc_ref(env);
    crate::lean_inc(const_name);
    let opt_decl = find_fn(env, const_name);
    if crate::lean_is_scalar(opt_decl) {
        // none: lean_box(0), no dec needed for scalars
        return None;
    }
    // some(decl): opt_decl is Option.some with tag 0, field 0 = decl
    let decl = crate::lean_ctor_get_export(opt_decl, 0);
    crate::lean_inc(decl);
    crate::lean_dec(opt_decl);
    // Lean.IR.Decl.fdecl/extern: field 1 is xs : Array Param
    let xs = crate::lean_ctor_get_export(decl, 1);
    let arity = crate::lean_array_size_export(xs) as u32;
    crate::lean_dec(decl);
    Some(arity)
}

#[no_mangle] pub unsafe extern "C" fn lean_mk_thunk(c: lean_obj_arg) -> lean_obj_res {
    let o = crate::lean_alloc_small_object_export(core::mem::size_of::<crate::LeanThunkObject>() as crate::Size) as *mut crate::LeanThunkObject;
    crate::lean_set_st_header(o as *mut LeanObject, LEAN_THUNK_TAG, 0);
    (*o).m_value = core::ptr::null_mut();
    (*o).m_closure = c;
    o as *mut LeanObject
}

#[no_mangle] pub unsafe extern "C" fn lean_thunk_pure(v: lean_obj_arg) -> lean_obj_res {
    let o = crate::lean_alloc_small_object_export(core::mem::size_of::<crate::LeanThunkObject>() as crate::Size) as *mut crate::LeanThunkObject;
    crate::lean_set_st_header(o as *mut LeanObject, LEAN_THUNK_TAG, 0);
    (*o).m_value = v;
    (*o).m_closure = core::ptr::null_mut();
    o as *mut LeanObject
}

#[no_mangle] pub unsafe extern "C" fn lean_thunk_get_own(t: b_lean_obj_arg) -> lean_obj_res {
    let o = t as *mut crate::LeanThunkObject;
    let r = (*o).m_value;
    let ret = if !r.is_null() { r } else { crate::runtime_object_array_impl::lean_thunk_get_core(t) };
    crate::lean_inc(ret);
    ret
}

#[no_mangle] pub unsafe extern "C" fn lean_task_spawn(c: lean_obj_arg, prio: lean_obj_arg) -> lean_obj_res {
    crate::lean_task_spawn_core(c, crate::lean_unbox(prio) as u32, false)
}

#[no_mangle] pub unsafe extern "C" fn lean_task_map(f: lean_obj_arg, t: lean_obj_arg, prio: lean_obj_arg, sync: u8) -> lean_obj_res {
    crate::lean_task_map_core(f, t, crate::lean_unbox(prio) as u32, sync != 0, false)
}

#[no_mangle] pub unsafe extern "C" fn lean_task_bind(x: lean_obj_arg, f: lean_obj_arg, prio: lean_obj_arg, sync: u8) -> lean_obj_res {
    crate::lean_task_bind_core(x, f, crate::lean_unbox(prio) as u32, sync != 0, false)
}

#[no_mangle] pub unsafe extern "C" fn lean_void_mk(a: lean_obj_arg) -> lean_obj_res {
    crate::lean_dec(a);
    crate::lean_box(0)
}

#[no_mangle] pub unsafe extern "C" fn lean_string_dec_lt(s1: b_lean_obj_arg, s2: b_lean_obj_arg) -> u8 {
    crate::runtime_object_string_impl::lean_string_lt(s1, s2) as u8
}

#[no_mangle] pub unsafe extern "C" fn lean_sarray_dec_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> u8 {
    if a1 == a2 {
        1
    } else {
        let sz1 = crate::lean_sarray_size(a1);
        let sz2 = crate::lean_sarray_size(a2);
        if sz1 == sz2 {
            crate::runtime_object_string_impl::lean_sarray_eq_cold(a1, a2) as u8
        } else {
            0
        }
    }
}

#[no_mangle] pub unsafe extern "C" fn lean_string_get_byte_fast(s: b_lean_obj_arg, i: b_lean_obj_arg) -> u8 {
    let str_ptr = crate::lean_string_cstr(s) as *const u8;
    let idx = crate::lean_unbox(i);
    *str_ptr.add(idx)
}

#[no_mangle] pub unsafe extern "C" fn lean_string_utf8_at_end(s: b_lean_obj_arg, i: b_lean_obj_arg) -> u8 {
    if !crate::lean_is_scalar(i) || crate::lean_unbox(i) >= crate::lean_string_size(s) - 1 {
        1
    } else {
        0
    }
}

#[no_mangle] pub unsafe extern "C" fn lean_is_exclusive_obj(o: *mut LeanObject) -> u8 {
    crate::lean_is_exclusive(o) as u8
}

#[no_mangle] pub unsafe extern "C" fn lean_get_max_ctor_fields(_unit: lean_obj_arg) -> lean_obj_res {
    crate::lean_box(256)
}

#[no_mangle] pub unsafe extern "C" fn lean_get_max_ctor_scalars_size(_unit: lean_obj_arg) -> lean_obj_res {
    crate::lean_box(1024)
}

#[no_mangle] pub unsafe extern "C" fn lean_get_max_ctor_tag(_unit: lean_obj_arg) -> lean_obj_res {
    crate::lean_box(LEAN_MAX_CTOR_TAG as usize)
}

#[no_mangle] pub unsafe extern "C" fn lean_get_usize_size(_unit: lean_obj_arg) -> lean_obj_res {
    crate::lean_box(core::mem::size_of::<usize>())
}

#[no_mangle] pub unsafe extern "C" fn lean_ptr_addr(o: *mut LeanObject) -> usize {
    o as usize
}

#[no_mangle] pub unsafe extern "C" fn lean_strict_and(a: u8, b: u8) -> u8 {
    (a != 0 && b != 0) as u8
}

#[no_mangle] pub unsafe extern "C" fn lean_strict_or(a: u8, b: u8) -> u8 {
    (a != 0 || b != 0) as u8
}

#[no_mangle] pub unsafe extern "C" fn lean_internal_is_stage0() -> u8 {
    0 // We are compiling stage1 or later
}

#[no_mangle] pub unsafe extern "C" fn lean_manual_get_root(_unit: lean_obj_arg) -> lean_obj_res {
    crate::lean_mk_string(b"\0".as_ptr() as *const i8)
}

#[no_mangle] pub unsafe extern "C" fn lean_runtime_hold(_a: b_lean_obj_arg) -> lean_obj_res {
    crate::lean_box(0)
}

#[no_mangle] pub unsafe extern "C" fn lean_run_init(
    _env: b_lean_obj_arg,
    _opts: b_lean_obj_arg,
    _decl: b_lean_obj_arg,
    _init_decl: b_lean_obj_arg,
    _world: lean_obj_arg,
) -> lean_obj_res {
    crate::lean_io_result_mk_ok_export(crate::lean_box(0))
}

// runModInitCore (sym : @& String) : IO Bool
// Looks up the module initialization symbol and calls it (if found).
// Returns true if found and called (so runInitAttrs skips re-running interpreted inits),
// false if not found (so runInitAttrs falls through to evalConst for each init decl).
// Matches C++ lean_run_mod_init_core in src/library/ir_interpreter.cpp.
#[no_mangle] pub unsafe extern "C" fn lean_run_mod_init_core(sym: b_lean_obj_arg) -> lean_obj_res {
    type InitFn = unsafe extern "C" fn(u8) -> *mut crate::LeanObject;
    let s = crate::lean_string_cstr(sym) as *const core::ffi::c_char;
    let cstr = core::ffi::CStr::from_ptr(s);
    let ptr = lookup_current_process_symbol(cstr);
    if ptr.is_null() {
        return crate::lean_io_result_mk_ok_export(crate::lean_box(0)); // false: not found
    }
    let init_fn: InitFn = core::mem::transmute(ptr);
    let r = init_fn(0); // builtin=0 (not a builtin library)
    if crate::lean_io_result_is_ok(r) {
        crate::lean_dec_ref(r);
        crate::lean_io_result_mk_ok_export(crate::lean_box(1)) // true: found and ran
    } else {
        r // propagate error
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_eval_const(
    env: b_lean_obj_arg,
    _opts: b_lean_obj_arg,
    const_name: b_lean_obj_arg,
) -> lean_obj_res {
    let Some(symbol) = mangle_name(const_name, "l_") else {
        return mk_except_error("cannot evaluate anonymous constant");
    };
    let boxed_symbol = format!("{symbol}___boxed");
    let Ok(c_boxed_symbol) = CString::new(boxed_symbol.as_str()) else {
        return mk_except_error("invalid native symbol name");
    };
    let Ok(c_symbol) = CString::new(symbol.as_str()) else {
        return mk_except_error("invalid native symbol name");
    };
    let boxed_addr = lookup_current_process_symbol(&c_boxed_symbol);
    let addr = if boxed_addr.is_null() {
        lookup_current_process_symbol(&c_symbol)
    } else {
        boxed_addr
    };
    if addr.is_null() {
        return mk_except_error(&format!("native symbol not found: {symbol}"));
    }
    // Use IR arity (real native parameter count) if available.
    // This correctly handles IO Unit functions which have 0 Lean-type Pi binders
    // but 1 native parameter (the IO world). Fallback to type-based arity for
    // constants without IR declarations (e.g. some extern decls).
    let arity = ir_decl_arity(env, const_name)
        .or_else(|| native_constant_arity(env, const_name))
        .unwrap_or(0);
    if arity > 0 {
        return mk_except_ok(crate::lean_alloc_closure_export(addr, arity, 0));
    }
    mk_except_ok(read_native_constant_or_call(addr))
}

#[no_mangle] pub unsafe extern "C" fn lean_eval_main() -> u32 { 1 }
#[no_mangle] pub unsafe extern "C" fn lean_expr_data(expr: lean_obj_arg) -> u64 {
    let offset = (crate::lean_ctor_num_objs(expr) as usize) * core::mem::size_of::<*mut ()>();
    crate::lean_ctor_get_uint64(expr, offset)
}
