/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod library_ir_interpreter_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ffi::{c_char, c_void};
    use core::ptr;
    use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering};
    #[cfg(unix)]
    use libloading::os::unix::Library as UnixLibrary;
    use std::collections::HashMap;
    use std::hash::{BuildHasher, Hash, Hasher};
    use std::sync::{Mutex, MutexGuard, OnceLock};

    // ---------------------------------------------------------------------------
    // FFI declarations
    // ---------------------------------------------------------------------------

    unsafe extern "C" {
        // IR declaration lookup
        fn lean_ir_find_env_decl(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;
        fn lean_ir_find_env_decl_boxed(env: *mut LeanObject, n: *mut LeanObject)
        -> *mut LeanObject;

        // Numeric coercions
        fn lean_float_of_nat(a: *mut LeanObject) -> f64;
        fn lean_float32_of_nat(a: *mut LeanObject) -> f32;
        fn lean_usize_of_big_nat(a: *mut LeanObject) -> usize;
        fn lean_uint64_of_big_nat(a: *mut LeanObject) -> u64;

        // Symbol name helpers
        fn lean_get_symbol_stem(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_mangled_boxed_name(s: *mut LeanObject) -> *mut LeanObject;

        // Init attribute
        fn lean_get_regular_init_fn_name_for(
            env: *mut LeanObject,
            n: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_get_export_name_for(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;

        // Name equality and hash
        fn lean_name_eq(n1: *mut LeanObject, n2: *mut LeanObject) -> u8;

        // Sorry dep check
        fn lean_decl_get_sorry_dep(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;

        // Elab environment of kernel env
        fn lean_elab_environment_of_kernel_env(env: *mut LeanObject) -> *mut LeanObject;

        // Option bool
        fn lean_options_get_bool(
            opts: *mut LeanObject,
            name: *mut LeanObject,
            default_value: bool,
        ) -> bool;

        // apply_n
        fn lean_apply_n(f: *mut LeanObject, n: u32, args: *mut *mut LeanObject) -> *mut LeanObject; // duplicate in src/rust/leanh/src/arity.rs at line 462 (🔁)

        // curry (call native function pointer with n boxed args)
        fn lean_curry(
            fun: *mut core::ffi::c_void,
            n: u32,
            args: *mut *mut LeanObject,
        ) -> *mut LeanObject;

        // IR format (debug)
        fn lean_ir_format_fn_body_head(b: *mut LeanObject) -> *mut LeanObject;

        // check_system
        fn lean_check_system(component_name: *const c_char, do_check_interrupted: bool);

        // time task
        fn lean_runtime_time_task_begin(
            category: *const c_char,
            opts: *mut LeanObject,
            name: *mut LeanObject,
        ) -> u8;
        fn lean_runtime_time_task_end(enabled: u8);

        // scope_trace_env (C++ RAII for trace opts)
        fn lean_scope_trace_env_ctor(
            this: *mut ScopeTraceEnv,
            env: *const *mut LeanObject,
            opts: *const *mut LeanObject,
        );
        fn lean_scope_trace_env_dtor(this: *mut ScopeTraceEnv);

        fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;

        // IO helpers
        fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool; // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 570 (🔁)
        fn lean_io_result_get_value(obj: *mut LeanObject) -> *mut LeanObject; // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 575 (🔁)
        fn lean_io_result_show_error(obj: *mut LeanObject); // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 583 (🔁)
        fn lean_io_result_mk_ok(val: *mut LeanObject) -> *mut LeanObject; // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 241 (🔁)
        fn lean_io_result_mk_error(err: *mut LeanObject) -> *mut LeanObject;

        // get_init_fn_name_for (already in lib.rs but may be called as extern)
        fn lean_get_init_fn_name_for(
            env: *mut LeanObject,
            name: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    // ---------------------------------------------------------------------------
    // Inline helpers (mirroring lean.h static inlines)
    // ---------------------------------------------------------------------------

    #[inline(always)]
    unsafe fn lean_ctor_get_obj(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
        (obj.add(1) as *mut *mut LeanObject).add(idx).read()
    }

    #[inline(always)]
    unsafe fn lean_ctor_set_obj(obj: *mut LeanObject, idx: usize, val: *mut LeanObject) {
        (obj.add(1) as *mut *mut LeanObject).add(idx).write(val);
    }

    #[inline(always)]
    unsafe fn lean_ctor_get_u8(obj: *mut LeanObject, byte_offset: usize) -> u8 {
        (obj.add(1) as *const u8).add(byte_offset).read()
    }

    #[inline(always)]
    unsafe fn lean_ctor_get_u16(obj: *mut LeanObject, byte_offset: usize) -> u16 {
        (obj.add(1) as *const u8)
            .add(byte_offset)
            .cast::<u16>()
            .read_unaligned()
    }

    #[inline(always)]
    unsafe fn lean_ctor_get_u32(obj: *mut LeanObject, byte_offset: usize) -> u32 {
        (obj.add(1) as *const u8)
            .add(byte_offset)
            .cast::<u32>()
            .read_unaligned()
    }

    #[inline(always)]
    unsafe fn lean_ctor_get_u64(obj: *mut LeanObject, byte_offset: usize) -> u64 {
        (obj.add(1) as *const u8)
            .add(byte_offset)
            .cast::<u64>()
            .read_unaligned()
    }

    #[inline(always)]
    unsafe fn lean_ctor_set_u8(obj: *mut LeanObject, byte_offset: usize, v: u8) {
        (obj.add(1) as *mut u8).add(byte_offset).write(v);
    }

    #[inline(always)]
    unsafe fn lean_ctor_set_u16(obj: *mut LeanObject, byte_offset: usize, v: u16) {
        (obj.add(1) as *mut u8)
            .add(byte_offset)
            .cast::<u16>()
            .write_unaligned(v);
    }

    #[inline(always)]
    unsafe fn lean_ctor_set_u32(obj: *mut LeanObject, byte_offset: usize, v: u32) {
        (obj.add(1) as *mut u8)
            .add(byte_offset)
            .cast::<u32>()
            .write_unaligned(v);
    }

    #[inline(always)]
    unsafe fn lean_ctor_set_u64(obj: *mut LeanObject, byte_offset: usize, v: u64) {
        (obj.add(1) as *mut u8)
            .add(byte_offset)
            .cast::<u64>()
            .write_unaligned(v);
    }

    #[inline(always)]
    unsafe fn lean_array_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
        (obj as *const u8)
            .add(24)
            .cast::<*mut LeanObject>()
            .add(idx)
            .read()
    }

    #[inline(always)]
    unsafe fn lean_uint64_of_nat(a: *mut LeanObject) -> u64 {
        if lean_is_scalar(a) {
            lean_unbox(a) as u64
        } else {
            lean_uint64_of_big_nat(a)
        }
    }

    #[inline(always)]
    unsafe fn lean_usize_of_nat(a: *mut LeanObject) -> usize {
        if lean_is_scalar(a) {
            lean_unbox(a)
        } else {
            lean_usize_of_big_nat(a)
        }
    }

    #[inline(always)]
    unsafe fn lean_io_mk_world() -> *mut LeanObject {
        lean_box(0)
    }

    unsafe fn lean_io_result_mk_error_str(msg: &str) -> *mut LeanObject {
        let c_msg = std::ffi::CString::new(msg).unwrap_or_default();
        let s = lean_mk_string(c_msg.as_ptr());
        let mut fields = [s];
        lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0) // IO.Error.userError
    }

    unsafe fn lean_io_result_mk_error_from_string_obj(msg: *mut LeanObject) -> *mut LeanObject {
        let mut fields = [msg];
        let ioe = lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0); // IO.Error.userError s
        lean_io_result_mk_error(ioe)
    }

    unsafe fn lean_io_result_mk_error_msg(msg: &str) -> *mut LeanObject {
        let c_msg = std::ffi::CString::new(msg).unwrap_or_default();
        let s = lean_mk_string(c_msg.as_ptr());
        lean_io_result_mk_error_from_string_obj(s)
    }

    // ---------------------------------------------------------------------------
    // scope_trace_env wrapper (C++ RAII moved to Rust manual dtor)
    // ---------------------------------------------------------------------------

    #[repr(C)]
    struct ScopeTraceEnv {
        m_old_opts: *const *mut LeanObject,
    }

    struct ScopeTraceEnvGuard {
        inner: ScopeTraceEnv,
        // Heap-allocate opts so the pointer passed to G_OPTS via lean_scope_trace_env_ctor
        // remains stable even after ScopeTraceEnvGuard is moved out of new().
        // Rust moves structs by bitwise copy; Box's heap allocation doesn't move.
        _boxed_opts: Box<*mut LeanObject>,
    }

    impl ScopeTraceEnvGuard {
        unsafe fn new(_env: *mut LeanObject, opts: *mut LeanObject) -> Self {
            let boxed_opts = Box::new(opts);
            let opts_ptr: *const *mut LeanObject = &*boxed_opts;
            let mut inner = ScopeTraceEnv {
                m_old_opts: ptr::null(),
            };
            // _env is unused in the Rust impl of scope_trace_env ctor
            lean_scope_trace_env_ctor(&mut inner, ptr::null(), opts_ptr);
            ScopeTraceEnvGuard {
                inner,
                _boxed_opts: boxed_opts,
            }
        }
    }

    impl Drop for ScopeTraceEnvGuard {
        fn drop(&mut self) {
            // Restore G_OPTS before _boxed_opts is freed (Drop runs before field drops).
            unsafe {
                lean_scope_trace_env_dtor(&mut self.inner);
            }
        }
    }

    // ---------------------------------------------------------------------------
    // time task guard
    // ---------------------------------------------------------------------------

    struct TimeTaskGuard {
        enabled: u8,
    }

    impl TimeTaskGuard {
        unsafe fn new(
            category: *const c_char,
            opts: *mut LeanObject,
            name: *mut LeanObject,
        ) -> Self {
            let enabled = lean_runtime_time_task_begin(category, opts, name);
            TimeTaskGuard { enabled }
        }
    }

    impl Drop for TimeTaskGuard {
        fn drop(&mut self) {
            unsafe {
                lean_runtime_time_task_end(self.enabled);
            }
        }
    }

    // ---------------------------------------------------------------------------
    // Name-keyed HashMap
    // ---------------------------------------------------------------------------

    // We need a HashMap keyed by Lean name objects using lean_name_hash / lean_name_eq.
    // We store the raw *mut LeanObject as key, with a custom hasher.

    #[derive(Clone, Copy)]
    struct NameKey(*mut LeanObject);

    // SAFETY: Lean name objects are pinned in memory and their identity doesn't change.
    // We only use NameKey in single-threaded interpreter contexts or behind a RwLock.
    unsafe impl Send for NameKey {}
    unsafe impl Sync for NameKey {}

    impl PartialEq for NameKey {
        fn eq(&self, other: &Self) -> bool {
            unsafe { lean_name_eq(self.0, other.0) != 0 }
        }
    }

    impl Eq for NameKey {}

    impl Hash for NameKey {
        fn hash<H: Hasher>(&self, state: &mut H) {
            unsafe {
                let h = lean_name_hash(self.0);
                state.write_u64(h);
            }
        }
    }

    unsafe fn lean_name_hash(n: *mut LeanObject) -> u64 {
        if lean_is_scalar(n) {
            1723u64
        } else {
            // Name hash is stored at offset sizeof(void*)*2 in the name ctor
            lean_ctor_get_u64(n, core::mem::size_of::<*mut LeanObject>() * 2)
        }
    }

    type NameHashMap<V> = HashMap<NameKey, V, NameBuildHasher>;

    fn new_name_hash_map<V>() -> NameHashMap<V> {
        HashMap::with_hasher(NameBuildHasher)
    }

    #[derive(Default, Clone)]
    struct NameBuildHasher;

    impl BuildHasher for NameBuildHasher {
        type Hasher = NameHasher;
        fn build_hasher(&self) -> Self::Hasher {
            NameHasher(0)
        }
    }

    struct NameHasher(u64);

    impl Hasher for NameHasher {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, bytes: &[u8]) {
            // Not used; NameKey::hash only calls write_u64
            for &b in bytes {
                self.0 = self.0.wrapping_mul(31).wrapping_add(b as u64);
            }
        }
        fn write_u64(&mut self, i: u64) {
            self.0 = i;
        }
    }

    // ---------------------------------------------------------------------------
    // IR type enum
    // ---------------------------------------------------------------------------

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    enum IrType {
        Float = 0,
        UInt8 = 1,
        UInt16 = 2,
        UInt32 = 3,
        UInt64 = 4,
        USize = 5,
        Irrelevant = 6,
        Object = 7,
        TObject = 8,
        Float32 = 9,
        Struct = 10,
        Union = 11,
        Tagged = 12,
        Void = 13,
    }

    impl IrType {
        fn is_scalar(self) -> bool {
            !matches!(
                self,
                IrType::Object
                    | IrType::Tagged
                    | IrType::TObject
                    | IrType::Irrelevant
                    | IrType::Void
            )
        }
    }

    unsafe fn to_ir_type(obj: *mut LeanObject) -> Result<IrType, String> {
        if !lean_is_scalar(obj) {
            return Err("unsupported IRType".to_string());
        }
        let n = lean_unbox(obj) as u8;
        match n {
            0 => Ok(IrType::Float),
            1 => Ok(IrType::UInt8),
            2 => Ok(IrType::UInt16),
            3 => Ok(IrType::UInt32),
            4 => Ok(IrType::UInt64),
            5 => Ok(IrType::USize),
            6 => Ok(IrType::Irrelevant),
            7 => Ok(IrType::Object),
            8 => Ok(IrType::TObject),
            9 => Ok(IrType::Float32),
            10 => Ok(IrType::Struct),
            11 => Ok(IrType::Union),
            12 => Ok(IrType::Tagged),
            13 => Ok(IrType::Void),
            _ => Err(format!("unknown IRType {}", n)),
        }
    }

    unsafe fn cnstr_get_ir_type(o: *mut LeanObject, i: usize) -> Result<IrType, String> {
        to_ir_type(lean_ctor_get_obj(o, i))
    }

    // ---------------------------------------------------------------------------
    // IR enum kinds
    // ---------------------------------------------------------------------------

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    enum ExprKind {
        Ctor = 0,
        Reset = 1,
        Reuse = 2,
        Proj = 3,
        UProj = 4,
        SProj = 5,
        FAp = 6,
        PAp = 7,
        Ap = 8,
        Box = 9,
        Unbox = 10,
        Lit = 11,
        IsShared = 12,
        IsTaggedPtr = 13,
    }

    unsafe fn expr_tag(e: *mut LeanObject) -> ExprKind {
        core::mem::transmute(lean_obj_tag(e))
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    enum LitValKind {
        Num = 0,
        Str = 1,
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    enum FnBodyKind {
        VDecl = 0,
        JDecl = 1,
        Set = 2,
        SetTag = 3,
        USet = 4,
        SSet = 5,
        Inc = 6,
        Dec = 7,
        Del = 8,
        Case = 9,
        Ret = 10,
        Jmp = 11,
        Unreachable = 12,
    }

    unsafe fn fn_body_tag(b: *mut LeanObject) -> FnBodyKind {
        core::mem::transmute(lean_obj_tag(b))
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    enum DeclKind {
        Fun = 0,
        Extern = 1,
    }

    unsafe fn decl_tag(d: *mut LeanObject) -> DeclKind {
        core::mem::transmute(lean_obj_tag(d))
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    enum AltCoreKind {
        Ctor = 0,
        Default = 1,
    }

    unsafe fn alt_core_tag(a: *mut LeanObject) -> AltCoreKind {
        core::mem::transmute(lean_obj_tag(a))
    }

    // ---------------------------------------------------------------------------
    // Bool field accessor (after obj pointer fields)
    // ---------------------------------------------------------------------------

    unsafe fn get_bool_field(o: *mut LeanObject, num_obj_fields: usize) -> bool {
        lean_ctor_get_u8(o, core::mem::size_of::<*mut LeanObject>() * num_obj_fields) != 0
    }

    // ---------------------------------------------------------------------------
    // IR AST field accessors
    // ---------------------------------------------------------------------------

    // arg
    unsafe fn arg_is_irrelevant(a: *mut LeanObject) -> bool {
        lean_is_scalar(a)
    }
    unsafe fn arg_var_id(a: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(a, 0)
    }

    // var_id: just a name (small value = variable index)
    unsafe fn var_get_small_value(v: *mut LeanObject) -> usize {
        lean_unbox(v)
    }

    // nat get_small_value: assumes it fits in usize
    unsafe fn nat_get_small_value(n: *mut LeanObject) -> usize {
        lean_usize_of_nat(n)
    }

    // lit_val
    unsafe fn lit_val_tag(l: *mut LeanObject) -> LitValKind {
        core::mem::transmute(lean_obj_tag(l))
    }
    unsafe fn lit_val_num(l: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(l, 0)
    }
    unsafe fn lit_val_str(l: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(l, 0)
    }

    // ctor_info
    unsafe fn ctor_info_tag_val(c: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(c, 1))
    }
    unsafe fn ctor_info_size(c: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(c, 2))
    }
    unsafe fn ctor_info_usize(c: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(c, 3))
    }
    unsafe fn ctor_info_ssize(c: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(c, 4))
    }

    // expr fields
    unsafe fn expr_ctor_info(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_ctor_args(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_reset_num_objs(e: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(e, 0))
    }
    unsafe fn expr_reset_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_reuse_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_reuse_ctor(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_reuse_args(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 2)
    }
    unsafe fn expr_reuse_update_header(e: *mut LeanObject) -> bool {
        get_bool_field(e, 3)
    }
    unsafe fn expr_proj_idx(e: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(e, 0))
    }
    unsafe fn expr_proj_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_uproj_idx(e: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(e, 0))
    }
    unsafe fn expr_uproj_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_sproj_idx(e: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(e, 0))
    }
    unsafe fn expr_sproj_offset(e: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(e, 1))
    }
    unsafe fn expr_sproj_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 2)
    }
    unsafe fn expr_fap_fun(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_fap_args(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_pap_fun(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_pap_args(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_ap_fun(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_ap_args(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_box_type(e: *mut LeanObject) -> Result<IrType, String> {
        cnstr_get_ir_type(e, 0)
    }
    unsafe fn expr_box_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 1)
    }
    unsafe fn expr_unbox_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_lit_val(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_is_shared_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }
    unsafe fn expr_is_tagged_ptr_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(e, 0)
    }

    // param
    unsafe fn param_var(p: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(p, 0)
    }
    unsafe fn param_type(p: *mut LeanObject) -> Result<IrType, String> {
        cnstr_get_ir_type(p, 1)
    }
    unsafe fn param_borrow(p: *mut LeanObject) -> bool {
        get_bool_field(p, 2)
    }

    // alt_core
    unsafe fn alt_core_ctor_info(a: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(a, 0)
    }
    unsafe fn alt_core_ctor_cont(a: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(a, 1)
    }
    unsafe fn alt_core_default_cont(a: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(a, 0)
    }

    // fn_body
    unsafe fn fn_body_vdecl_var(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_vdecl_type(b: *mut LeanObject) -> Result<IrType, String> {
        cnstr_get_ir_type(b, 1)
    }
    unsafe fn fn_body_vdecl_expr(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 2)
    }
    unsafe fn fn_body_vdecl_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 3)
    }
    unsafe fn fn_body_jdecl_id(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_jdecl_params(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 1)
    }
    unsafe fn fn_body_jdecl_body(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 2)
    }
    unsafe fn fn_body_jdecl_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 3)
    }
    unsafe fn fn_body_set_var(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_set_idx(b: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(b, 1))
    }
    unsafe fn fn_body_set_arg(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 2)
    }
    unsafe fn fn_body_set_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 3)
    }
    unsafe fn fn_body_set_tag_var(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_set_tag_cidx(b: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(b, 1))
    }
    unsafe fn fn_body_set_tag_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 2)
    }
    unsafe fn fn_body_uset_target(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_uset_idx(b: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(b, 1))
    }
    unsafe fn fn_body_uset_source(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 2)
    }
    unsafe fn fn_body_uset_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 3)
    }
    unsafe fn fn_body_sset_target(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_sset_idx(b: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(b, 1))
    }
    unsafe fn fn_body_sset_offset(b: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(b, 2))
    }
    unsafe fn fn_body_sset_source(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 3)
    }
    unsafe fn fn_body_sset_type(b: *mut LeanObject) -> Result<IrType, String> {
        cnstr_get_ir_type(b, 4)
    }
    unsafe fn fn_body_sset_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 5)
    }
    unsafe fn fn_body_inc_var(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_inc_val(b: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(b, 1))
    }
    unsafe fn fn_body_inc_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 2)
    }
    unsafe fn fn_body_dec_var(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_dec_val(b: *mut LeanObject) -> usize {
        nat_get_small_value(lean_ctor_get_obj(b, 1))
    }
    unsafe fn fn_body_dec_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 2)
    }
    unsafe fn fn_body_del_var(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_del_cont(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 1)
    }
    unsafe fn fn_body_case_var(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 1)
    }
    unsafe fn fn_body_case_var_type(b: *mut LeanObject) -> Result<IrType, String> {
        cnstr_get_ir_type(b, 2)
    }
    unsafe fn fn_body_case_alts(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 3)
    }
    unsafe fn fn_body_ret_arg(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_jmp_jp(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 0)
    }
    unsafe fn fn_body_jmp_args(b: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(b, 1)
    }

    // decl
    unsafe fn decl_fun_id(d: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(d, 0)
    }
    unsafe fn decl_params(d: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get_obj(d, 1)
    }
    unsafe fn decl_type_field(d: *mut LeanObject) -> Result<IrType, String> {
        cnstr_get_ir_type(d, 2)
    }
    unsafe fn decl_params_size(d: *mut LeanObject) -> usize {
        lean_array_size(decl_params(d))
    }
    unsafe fn decl_params_get(d: *mut LeanObject, i: usize) -> *mut LeanObject {
        lean_array_get(decl_params(d), i)
    }
    unsafe fn decl_fun_body(d: *mut LeanObject) -> Result<*mut LeanObject, String> {
        if decl_tag(d) != DeclKind::Fun {
            let fn_id = decl_fun_id(d);
            let name_str = lean_name_to_string_for_err(fn_id);
            return Err(format!(
                "(interpreter) IR of declaration '{}' not available; this may point to a missing `meta` check in a metaprogram",
                name_str
            ));
        }
        Ok(lean_ctor_get_obj(d, 3))
    }

    // array field accessors
    unsafe fn array_size(arr: *mut LeanObject) -> usize {
        lean_array_size(arr)
    }
    unsafe fn array_get(arr: *mut LeanObject, i: usize) -> *mut LeanObject {
        lean_array_get(arr, i)
    }

    // Simple best-effort name to string for error messages
    unsafe fn lean_name_to_string_for_err(n: *mut LeanObject) -> String {
        if lean_is_scalar(n) {
            return "<anonymous>".to_string();
        }
        // Walk the name spine collecting components
        let mut components: Vec<String> = Vec::new();
        let mut cur = n;
        while !lean_is_scalar(cur) {
            let tag = lean_obj_tag(cur);
            match tag {
                1 => {
                    // Name.str prefix str
                    let str_obj = lean_ctor_get_obj(cur, 1);
                    let cstr = lean_string_cstr(str_obj);
                    let s = core::ffi::CStr::from_ptr(cstr)
                        .to_string_lossy()
                        .into_owned();
                    components.push(s);
                    cur = lean_ctor_get_obj(cur, 0);
                }
                2 => {
                    // Name.num prefix n
                    let num_obj = lean_ctor_get_obj(cur, 1);
                    let n = lean_usize_of_nat(num_obj);
                    components.push(n.to_string());
                    cur = lean_ctor_get_obj(cur, 0);
                }
                _ => break,
            }
        }
        components.reverse();
        components.join(".")
    }

    // ---------------------------------------------------------------------------
    // IR value type (union equivalent)
    // ---------------------------------------------------------------------------

    // We represent IrValue as a u64-sized union. The IR type system guarantees
    // correct interpretation at all times.
    #[derive(Clone, Copy)]
    union IrValue {
        m_num: u64,
        m_float: f64,
        m_float32: f32,
        m_obj: *mut LeanObject,
    }

    impl IrValue {
        #[inline]
        fn from_num(n: u64) -> Self {
            IrValue { m_num: n }
        }
        #[inline]
        fn from_float(f: f64) -> Self {
            IrValue { m_float: f }
        }
        #[inline]
        fn from_float32(f: f32) -> Self {
            IrValue { m_float32: f }
        }
        #[inline]
        fn from_obj(o: *mut LeanObject) -> Self {
            IrValue { m_obj: o }
        }
        #[inline]
        unsafe fn num(self) -> u64 {
            self.m_num
        }
        #[inline]
        unsafe fn float(self) -> f64 {
            self.m_float
        }
        #[inline]
        unsafe fn float32(self) -> f32 {
            self.m_float32
        }
        #[inline]
        unsafe fn obj(self) -> *mut LeanObject {
            self.m_obj
        }
    }

    unsafe fn box_t(v: IrValue, t: IrType) -> Result<*mut LeanObject, String> {
        Ok(match t {
            IrType::Float => lean_box_float(v.float()),
            IrType::Float32 => lean_box_float32(v.float32()),
            IrType::UInt8 => lean_box(v.num() as usize),
            IrType::UInt16 => lean_box(v.num() as usize),
            IrType::UInt32 => lean_box_uint32(v.num() as u32),
            IrType::UInt64 => lean_box_uint64(v.num()),
            IrType::USize => lean_box_size_t(v.num() as usize),
            IrType::Object
            | IrType::Tagged
            | IrType::TObject
            | IrType::Irrelevant
            | IrType::Void => v.obj(),
            IrType::Struct | IrType::Union => return Err("box_t: not implemented yet".to_string()),
        })
    }

    unsafe fn lean_box_size_t(n: usize) -> *mut LeanObject {
        let obj = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<usize>() as u32);
        lean_ctor_set_usize(obj, 0, n);
        obj
    }

    unsafe fn lean_unbox_size_t(o: *mut LeanObject) -> usize {
        lean_ctor_get_usize(o, 0)
    }

    unsafe fn unbox_t(o: *mut LeanObject, t: IrType) -> Result<IrValue, String> {
        Ok(match t {
            IrType::Float => IrValue::from_float(lean_unbox_float(o)),
            IrType::Float32 => IrValue::from_float32(lean_unbox_float32(o)),
            IrType::UInt8 => IrValue::from_num(lean_unbox(o) as u64),
            IrType::UInt16 => IrValue::from_num(lean_unbox(o) as u64),
            IrType::UInt32 => IrValue::from_num(lean_unbox_uint32(o) as u64),
            IrType::UInt64 => IrValue::from_num(lean_unbox_uint64(o)),
            IrType::USize => IrValue::from_num(lean_unbox_size_t(o) as u64),
            IrType::Struct | IrType::Union => {
                return Err("unbox_t: not implemented yet".to_string());
            }
            _ => unreachable!("unbox_t called with non-scalar type"),
        })
    }

    // ---------------------------------------------------------------------------
    // Platform symbol lookup
    // ---------------------------------------------------------------------------

    unsafe fn lookup_symbol_in_cur_exe(sym: *const c_char) -> *mut core::ffi::c_void {
        #[cfg(unix)]
        {
            let lib = UnixLibrary::this();
            let Ok(symbol) = (unsafe { lib.get::<*mut core::ffi::c_void>(CStr::from_ptr(sym)) })
            else {
                return ptr::null_mut();
            };
            *symbol
        }
        #[cfg(not(unix))]
        {
            ptr::null_mut()
        }
    }

    // ---------------------------------------------------------------------------
    // Global state
    // ---------------------------------------------------------------------------

    #[derive(Clone, Copy)]
    struct NativeSymbolCacheEntry {
        m_addr: *mut core::ffi::c_void,
        m_boxed: bool,
    }

    unsafe impl Send for NativeSymbolCacheEntry {}
    unsafe impl Sync for NativeSymbolCacheEntry {}

    // Values that are incremented and stored as "persistent"
    struct InitGlobals(NameHashMap<*mut LeanObject>);
    unsafe impl Send for InitGlobals {}
    unsafe impl Sync for InitGlobals {}

    struct NativeSymbolCache(NameHashMap<NativeSymbolCacheEntry>);
    unsafe impl Send for NativeSymbolCache {}
    unsafe impl Sync for NativeSymbolCache {}

    static G_INTERPRETER_PREFER_NATIVE_NAME: AtomicPtr<LeanObject> =
        AtomicPtr::new(ptr::null_mut());
    static G_INTERPRETER_KEY: AtomicUsize = AtomicUsize::new(0);
    static G_INTERPRETER_KEY_INIT: AtomicBool = AtomicBool::new(false);
    static mut G_INIT_GLOBALS: *mut InitGlobals = ptr::null_mut();
    static mut G_NATIVE_SYMBOL_CACHE: *mut NativeSymbolCache = ptr::null_mut();
    static G_NATIVE_SYMBOL_CACHE_MUTEX: OnceLock<Mutex<()>> = OnceLock::new();

    unsafe fn init_globals() -> &'static mut InitGlobals {
        if G_INIT_GLOBALS.is_null() {
            G_INIT_GLOBALS = Box::into_raw(Box::new(InitGlobals(new_name_hash_map())));
        }
        &mut *G_INIT_GLOBALS
    }

    unsafe fn native_symbol_cache() -> &'static mut NativeSymbolCache {
        if G_NATIVE_SYMBOL_CACHE.is_null() {
            G_NATIVE_SYMBOL_CACHE = Box::into_raw(Box::new(NativeSymbolCache(new_name_hash_map())));
        }
        &mut *G_NATIVE_SYMBOL_CACHE
    }

    fn native_symbol_cache_lock() -> MutexGuard<'static, ()> {
        G_NATIVE_SYMBOL_CACHE_MUTEX
            .get_or_init(|| Mutex::new(()))
            .lock()
            .expect("native symbol cache mutex poisoned")
    }

    unsafe fn interpreter_prefer_native_name() -> *mut LeanObject {
        let existing = G_INTERPRETER_PREFER_NATIVE_NAME.load(Ordering::Acquire);
        if !existing.is_null() {
            return existing;
        }

        let interp_str = lean_mk_string(c"interpreter".as_ptr());
        let prefer_native_str = lean_mk_string(c"prefer_native".as_ptr());
        let interp_name = lean_name_mk_string(lean_box(0), interp_str);
        let prefer_native_name = lean_name_mk_string(interp_name, prefer_native_str);
        // This name is a process-lifetime immortal global read concurrently from many
        // worker threads (every `Interpreter::new` does a non-atomic `lean_inc`/consume on
        // it via `lean_options_get_bool`). Mark it persistent (rc = 0, inc/dec become
        // no-ops) BEFORE publishing it, so those refcount operations are thread-safe.
        // Mirrors C++ `mark_persistent(g_verbose->raw())` for global option names
        // (util/options.cpp) and the kernel's `init_global_name`. Without this, the
        // non-atomic refcount races and is over-freed under parallel `try?`/library-search.
        lean_mark_persistent(prefer_native_name);
        match G_INTERPRETER_PREFER_NATIVE_NAME.compare_exchange(
            ptr::null_mut(),
            prefer_native_name,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => prefer_native_name,
            Err(current) => {
                // Lost the init race: our copy is already persistent so it cannot be
                // freed via `lean_dec` (no-op on rc = 0). This leaks a handful of small
                // Name objects exactly once per process, only when two threads initialize
                // simultaneously — negligible and bounded.
                current
            }
        }
    }

    unsafe fn interpreter_key() -> libc::pthread_key_t {
        if !G_INTERPRETER_KEY_INIT.load(Ordering::Acquire) {
            let mut key: libc::pthread_key_t = 0;
            let rc = libc::pthread_key_create(&mut key, None);
            assert_eq!(rc, 0);
            if G_INTERPRETER_KEY_INIT
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                G_INTERPRETER_KEY.store(key as usize, Ordering::Release);
            } else {
                libc::pthread_key_delete(key);
            }
        }
        G_INTERPRETER_KEY.load(Ordering::Acquire) as libc::pthread_key_t
    }

    unsafe fn get_interpreter() -> *mut Interpreter {
        libc::pthread_getspecific(interpreter_key()) as *mut Interpreter
    }

    unsafe fn set_interpreter(interp: *mut Interpreter) {
        let rc = libc::pthread_setspecific(interpreter_key(), interp as *mut c_void);
        assert_eq!(rc, 0);
    }

    const LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE: bool = true;

    // ---------------------------------------------------------------------------
    // Interpreter struct
    // ---------------------------------------------------------------------------

    struct Frame {
        m_fn: *mut LeanObject, // name (borrowed, env owns it)
        m_arg_bp: usize,
        m_jp_bp: usize,
    }

    struct ConstantCacheEntry {
        m_is_scalar: bool,
        m_val: IrValue,
    }

    #[derive(Clone, Copy)]
    struct SymbolCacheEntry {
        m_decl: *mut LeanObject, // decl (owned inc ref)
        m_native: NativeSymbolCacheEntry,
    }

    unsafe impl Send for SymbolCacheEntry {}
    unsafe impl Sync for SymbolCacheEntry {}

    struct Interpreter {
        m_arg_stack: Vec<IrValue>,
        m_jp_stack: Vec<*mut LeanObject>, // fn_body* pointers (borrowed from IR)
        m_call_stack: Vec<Frame>,
        m_env: *mut LeanObject,  // borrowed
        m_opts: *mut LeanObject, // borrowed
        m_prefer_native: bool,
        m_constant_cache: NameHashMap<ConstantCacheEntry>,
        m_symbol_cache: NameHashMap<SymbolCacheEntry>,
    }

    unsafe impl Send for Interpreter {}

    impl Interpreter {
        unsafe fn new(env: *mut LeanObject, opts: *mut LeanObject) -> Self {
            let name_obj = interpreter_prefer_native_name();
            lean_inc(name_obj);
            lean_inc(opts);
            let prefer_native =
                lean_options_get_bool(opts, name_obj, LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE);
            Interpreter {
                m_arg_stack: Vec::new(),
                m_jp_stack: Vec::new(),
                m_call_stack: Vec::new(),
                m_env: env,
                m_opts: opts,
                m_prefer_native: prefer_native,
                m_constant_cache: new_name_hash_map(),
                m_symbol_cache: new_name_hash_map(),
            }
        }

        // -----------------------------------------------------------------------
        // Frame management
        // -----------------------------------------------------------------------

        unsafe fn get_frame_arg_bp(&self) -> usize {
            self.m_call_stack.last().unwrap().m_arg_bp
        }

        unsafe fn get_frame_jp_bp(&self) -> usize {
            self.m_call_stack.last().unwrap().m_jp_bp
        }

        unsafe fn get_frame_fn(&self) -> *mut LeanObject {
            self.m_call_stack.last().unwrap().m_fn
        }

        unsafe fn var_slot(&mut self, v: *mut LeanObject) -> &mut IrValue {
            let i = self.get_frame_arg_bp() + var_get_small_value(v) - 1;
            if i >= self.m_arg_stack.len() {
                self.m_arg_stack.resize(i + 1, IrValue::from_num(0));
            }
            &mut self.m_arg_stack[i]
        }

        unsafe fn eval_arg(&mut self, a: *mut LeanObject) -> IrValue {
            if arg_is_irrelevant(a) {
                IrValue::from_obj(lean_box(0))
            } else {
                *self.var_slot(arg_var_id(a))
            }
        }

        unsafe fn push_frame(&mut self, d: *mut LeanObject, arg_bp: usize) {
            let fn_name = decl_fun_id(d);
            self.m_call_stack.push(Frame {
                m_fn: fn_name,
                m_arg_bp: arg_bp,
                m_jp_bp: self.m_jp_stack.len(),
            });
        }

        unsafe fn pop_frame(&mut self) {
            let frame = self.m_call_stack.pop().unwrap();
            self.m_arg_stack.truncate(frame.m_arg_bp);
            self.m_jp_stack.truncate(frame.m_jp_bp);
        }

        // -----------------------------------------------------------------------
        // alloc_ctor
        // -----------------------------------------------------------------------

        unsafe fn alloc_ctor(
            &mut self,
            info: *mut LeanObject,
            args: *mut LeanObject,
        ) -> *mut LeanObject {
            let tag = ctor_info_tag_val(info);
            let size = ctor_info_size(info);
            let usize_fields = ctor_info_usize(info);
            let ssize = ctor_info_ssize(info);
            if size == 0 && usize_fields == 0 && ssize == 0 {
                return lean_box(tag);
            }
            let o = lean_alloc_ctor(
                tag as u32,
                size,
                usize_fields * core::mem::size_of::<*mut LeanObject>() + ssize,
            );
            let n = array_size(args);
            for i in 0..n {
                let arg = array_get(args, i);
                lean_ctor_set_obj(o, i, self.eval_arg(arg).obj());
            }
            o
        }

        // -----------------------------------------------------------------------
        // mk_stub_closure
        // -----------------------------------------------------------------------

        unsafe fn mk_stub_closure(
            &self,
            d: *mut LeanObject,
            n: usize,
            args: *const *mut LeanObject,
        ) -> *mut LeanObject {
            let num_params = decl_params_size(d);
            let cls_size = 3 + num_params;
            let fun_ptr = get_stub(cls_size as u32);
            let cls = lean_alloc_closure(fun_ptr, cls_size as u32, (3 + n) as u32);
            lean_inc(self.m_env);
            lean_closure_set(cls, 0, self.m_env);
            lean_inc(self.m_opts);
            lean_closure_set(cls, 1, self.m_opts);
            lean_inc(d);
            lean_closure_set(cls, 2, d);
            for i in 0..n {
                lean_closure_set(cls, 3 + i, *args.add(i));
            }
            cls
        }

        // -----------------------------------------------------------------------
        // check_system
        // -----------------------------------------------------------------------

        unsafe fn check_system(&self) -> Result<(), String> {
            // Call check_stack and check_memory (not the heartbeat check)
            lean_check_system(c"interpreter".as_ptr(), false);
            Ok(())
        }

        // -----------------------------------------------------------------------
        // eval_expr
        // -----------------------------------------------------------------------

        unsafe fn eval_expr(&mut self, e: *mut LeanObject, t: IrType) -> Result<IrValue, String> {
            match expr_tag(e) {
                ExprKind::Ctor => {
                    let info = expr_ctor_info(e);
                    let args = expr_ctor_args(e);
                    Ok(IrValue::from_obj(self.alloc_ctor(info, args)))
                }
                ExprKind::Reset => {
                    let o = self.var_slot(expr_reset_obj(e)).obj();
                    if lean_is_exclusive(o) {
                        for i in 0..expr_reset_num_objs(e) {
                            lean_ctor_release(o, i);
                        }
                        Ok(IrValue::from_obj(o))
                    } else {
                        lean_dec(o);
                        Ok(IrValue::from_obj(lean_box(0)))
                    }
                }
                ExprKind::Reuse => {
                    let o = self.var_slot(expr_reuse_obj(e)).obj();
                    if lean_is_scalar(o) {
                        let ctor = expr_reuse_ctor(e);
                        let args = expr_reuse_args(e);
                        Ok(IrValue::from_obj(self.alloc_ctor(ctor, args)))
                    } else {
                        if expr_reuse_update_header(e) {
                            let new_tag = ctor_info_tag_val(expr_reuse_ctor(e));
                            (*o).tag = new_tag as u8;
                        }
                        let args = expr_reuse_args(e);
                        let n = array_size(args);
                        for i in 0..n {
                            let arg = array_get(args, i);
                            lean_ctor_set_obj(o, i, self.eval_arg(arg).obj());
                        }
                        Ok(IrValue::from_obj(o))
                    }
                }
                ExprKind::Proj => {
                    let o = self.var_slot(expr_proj_obj(e)).obj();
                    Ok(IrValue::from_obj(lean_ctor_get_obj(o, expr_proj_idx(e))))
                }
                ExprKind::UProj => {
                    let o = self.var_slot(expr_uproj_obj(e)).obj();
                    let v = lean_ctor_get_usize(o, expr_uproj_idx(e));
                    Ok(IrValue::from_num(v as u64))
                }
                ExprKind::SProj => {
                    let ptr_size = core::mem::size_of::<*mut LeanObject>();
                    let offset = expr_sproj_idx(e) * ptr_size + expr_sproj_offset(e);
                    let o = self.var_slot(expr_sproj_obj(e)).obj();
                    match t {
                        IrType::Float => Ok(IrValue::from_float(lean_ctor_get_float(o, offset))),
                        IrType::Float32 => {
                            Ok(IrValue::from_float32(lean_ctor_get_float32(o, offset)))
                        }
                        IrType::UInt8 => Ok(IrValue::from_num(lean_ctor_get_u8(o, offset) as u64)),
                        IrType::UInt16 => {
                            Ok(IrValue::from_num(lean_ctor_get_u16(o, offset) as u64))
                        }
                        IrType::UInt32 => {
                            Ok(IrValue::from_num(lean_ctor_get_u32(o, offset) as u64))
                        }
                        IrType::UInt64 => Ok(IrValue::from_num(lean_ctor_get_u64(o, offset))),
                        _ => Err("invalid instruction".to_string()),
                    }
                }
                ExprKind::FAp => {
                    let fn_name = expr_fap_fun(e);
                    let args = expr_fap_args(e);
                    if array_size(args) > 0 {
                        self.call(fn_name, args)
                    } else {
                        self.load(fn_name, t)
                    }
                }
                ExprKind::PAp => {
                    let fn_name = expr_pap_fun(e);
                    let sym = self.lookup_symbol(fn_name)?;
                    let pargs = expr_pap_args(e);
                    let n = array_size(pargs);
                    if !sym.m_native.m_addr.is_null() {
                        let arity = decl_params_size(sym.m_decl) as u32;
                        let cls = lean_alloc_closure(sym.m_native.m_addr, arity, n as u32);
                        for i in 0..n {
                            let arg = array_get(pargs, i);
                            lean_closure_set(cls, i, self.eval_arg(arg).obj());
                        }
                        Ok(IrValue::from_obj(cls))
                    } else {
                        let mut args_buf: Vec<*mut LeanObject> = Vec::with_capacity(n);
                        for i in 0..n {
                            args_buf.push(self.eval_arg(array_get(pargs, i)).obj());
                        }
                        let cls = self.mk_stub_closure(sym.m_decl, n, args_buf.as_ptr());
                        Ok(IrValue::from_obj(cls))
                    }
                }
                ExprKind::Ap => {
                    let ap_args = expr_ap_args(e);
                    let n = array_size(ap_args);
                    let mut args_buf: Vec<*mut LeanObject> = Vec::with_capacity(n);
                    for i in 0..n {
                        args_buf.push(self.eval_arg(array_get(ap_args, i)).obj());
                    }
                    let fun = self.var_slot(expr_ap_fun(e)).obj();
                    let r = lean_apply_n(fun, n as u32, args_buf.as_mut_ptr());
                    Ok(IrValue::from_obj(r))
                }
                ExprKind::Box => {
                    let inner_v = self.var_slot(expr_box_obj(e)).num();
                    let box_type = expr_box_type(e)?;
                    let boxed = box_t(IrValue::from_num(inner_v), box_type)?;
                    Ok(IrValue::from_obj(boxed))
                }
                ExprKind::Unbox => {
                    let o = self.var_slot(expr_unbox_obj(e)).obj();
                    unbox_t(o, t)
                }
                ExprKind::Lit => {
                    let lv = expr_lit_val(e);
                    match lit_val_tag(lv) {
                        LitValKind::Num => {
                            let n_obj = lit_val_num(lv);
                            match t {
                                IrType::Float => {
                                    lean_inc(n_obj);
                                    Ok(IrValue::from_float(lean_float_of_nat(n_obj)))
                                }
                                IrType::Float32 => {
                                    lean_inc(n_obj);
                                    Ok(IrValue::from_float32(lean_float32_of_nat(n_obj)))
                                }
                                IrType::UInt8 | IrType::UInt16 | IrType::UInt32 | IrType::USize => {
                                    Ok(IrValue::from_num(lean_usize_of_nat(n_obj) as u64))
                                }
                                IrType::UInt64 => Ok(IrValue::from_num(lean_uint64_of_nat(n_obj))),
                                IrType::Object | IrType::Tagged | IrType::TObject => {
                                    lean_inc(n_obj);
                                    Ok(IrValue::from_obj(n_obj))
                                }
                                _ => Err("invalid instruction".to_string()),
                            }
                        }
                        LitValKind::Str => {
                            let s = lit_val_str(lv);
                            lean_inc(s);
                            Ok(IrValue::from_obj(s))
                        }
                    }
                }
                ExprKind::IsShared => {
                    let o = self.var_slot(expr_is_shared_obj(e)).obj();
                    Ok(IrValue::from_num(!lean_is_exclusive(o) as u64))
                }
                ExprKind::IsTaggedPtr => {
                    let o = self.var_slot(expr_is_tagged_ptr_obj(e)).obj();
                    Ok(IrValue::from_num(!lean_is_scalar(o) as u64))
                }
            }
        }

        // -----------------------------------------------------------------------
        // eval_body
        // -----------------------------------------------------------------------

        unsafe fn eval_body(&mut self, b0: *mut LeanObject) -> Result<IrValue, String> {
            self.check_system()?;
            let mut b = b0;
            loop {
                match fn_body_tag(b) {
                    FnBodyKind::VDecl => {
                        let var = fn_body_vdecl_var(b);
                        let ty = fn_body_vdecl_type(b)?;
                        let expr = fn_body_vdecl_expr(b);
                        let cont = fn_body_vdecl_cont(b);

                        // Tail recursion check
                        if expr_tag(expr) == ExprKind::FAp {
                            let fn_name = expr_fap_fun(expr);
                            let cur_fn = self.get_frame_fn();
                            let fap_args = expr_fap_args(expr);
                            if lean_name_eq(fn_name, cur_fn) != 0
                                && fn_body_tag(cont) == FnBodyKind::Ret
                                && !arg_is_irrelevant(fn_body_ret_arg(cont))
                                && lean_name_eq(arg_var_id(fn_body_ret_arg(cont)), var) != 0
                            {
                                // tail recursion: copy arg values to param slots
                                let n = array_size(fap_args);
                                let old_size = self.m_arg_stack.len();
                                for i in 0..n {
                                    let v = self.eval_arg(array_get(fap_args, i));
                                    self.m_arg_stack.push(v);
                                }
                                let arg_bp = self.get_frame_arg_bp();
                                for i in 0..n {
                                    self.m_arg_stack[arg_bp + i] = self.m_arg_stack[old_size + i];
                                }
                                self.m_arg_stack.truncate(arg_bp + n);
                                b = b0;
                                self.check_system()?;
                                continue;
                            }
                        }

                        let v = self.eval_expr(expr, ty)?;
                        *self.var_slot(var) = v;
                        b = cont;
                    }
                    FnBodyKind::JDecl => {
                        let jp_id = fn_body_jdecl_id(b);
                        let jp_idx = self.get_frame_jp_bp() + var_get_small_value(jp_id);
                        if jp_idx >= self.m_jp_stack.len() {
                            self.m_jp_stack.resize(jp_idx + 1, ptr::null_mut());
                        }
                        self.m_jp_stack[jp_idx] = b;
                        b = fn_body_jdecl_cont(b);
                    }
                    FnBodyKind::Set => {
                        let o = self.var_slot(fn_body_set_var(b)).obj();
                        let idx = fn_body_set_idx(b);
                        let arg = fn_body_set_arg(b);
                        lean_ctor_set_obj(o, idx, self.eval_arg(arg).obj());
                        b = fn_body_set_cont(b);
                    }
                    FnBodyKind::SetTag => {
                        let o = self.var_slot(fn_body_set_tag_var(b)).obj();
                        let tag = fn_body_set_tag_cidx(b);
                        (*o).tag = tag as u8;
                        b = fn_body_set_tag_cont(b);
                    }
                    FnBodyKind::USet => {
                        let o = self.var_slot(fn_body_uset_target(b)).obj();
                        let idx = fn_body_uset_idx(b);
                        let src = self.var_slot(fn_body_uset_source(b)).num() as usize;
                        lean_ctor_set_usize(o, idx, src);
                        b = fn_body_uset_cont(b);
                    }
                    FnBodyKind::SSet => {
                        let o = self.var_slot(fn_body_sset_target(b)).obj();
                        let ptr_size = core::mem::size_of::<*mut LeanObject>();
                        let offset = fn_body_sset_idx(b) * ptr_size + fn_body_sset_offset(b);
                        let v = *self.var_slot(fn_body_sset_source(b));
                        match fn_body_sset_type(b)? {
                            IrType::Float => lean_ctor_set_float(o, offset, v.float()),
                            IrType::Float32 => lean_ctor_set_float32(o, offset, v.float32()),
                            IrType::UInt8 => lean_ctor_set_u8(o, offset, v.num() as u8),
                            IrType::UInt16 => lean_ctor_set_u16(o, offset, v.num() as u16),
                            IrType::UInt32 => lean_ctor_set_u32(o, offset, v.num() as u32),
                            IrType::UInt64 => lean_ctor_set_u64(o, offset, v.num()),
                            _ => return Err("invalid instruction".to_string()),
                        }
                        b = fn_body_sset_cont(b);
                    }
                    FnBodyKind::Inc => {
                        let o = self.var_slot(fn_body_inc_var(b)).obj();
                        let n = fn_body_inc_val(b);
                        lean_inc_n(o, n);
                        b = fn_body_inc_cont(b);
                    }
                    FnBodyKind::Dec => {
                        let o = self.var_slot(fn_body_dec_var(b)).obj();
                        let n = fn_body_dec_val(b);
                        for _ in 0..n {
                            lean_dec(o);
                        }
                        b = fn_body_dec_cont(b);
                    }
                    FnBodyKind::Del => {
                        let o = self.var_slot(fn_body_del_var(b)).obj();
                        lean_del_object(o);
                        b = fn_body_del_cont(b);
                    }
                    FnBodyKind::Case => {
                        let alts = fn_body_case_alts(b);
                        let case_var = fn_body_case_var(b);
                        let case_type = fn_body_case_var_type(b)?;
                        let v = *self.var_slot(case_var);
                        let tag: usize = if case_type.is_scalar() {
                            v.num() as usize
                        } else {
                            lean_obj_tag(v.obj()) as usize
                        };
                        let n_alts = array_size(alts);
                        let mut found = false;
                        for i in 0..n_alts {
                            let alt = array_get(alts, i);
                            match alt_core_tag(alt) {
                                AltCoreKind::Ctor => {
                                    let ctor_tag = ctor_info_tag_val(alt_core_ctor_info(alt));
                                    if tag == ctor_tag {
                                        b = alt_core_ctor_cont(alt);
                                        found = true;
                                        break;
                                    }
                                }
                                AltCoreKind::Default => {
                                    b = alt_core_default_cont(alt);
                                    found = true;
                                    break;
                                }
                            }
                        }
                        if !found {
                            return Err("incomplete case".to_string());
                        }
                    }
                    FnBodyKind::Ret => {
                        return Ok(self.eval_arg(fn_body_ret_arg(b)));
                    }
                    FnBodyKind::Jmp => {
                        let jp_id = fn_body_jmp_jp(b);
                        let jp_idx = self.get_frame_jp_bp() + var_get_small_value(jp_id);
                        let jp = self.m_jp_stack[jp_idx];
                        let jp_params = fn_body_jdecl_params(jp);
                        let jmp_args = fn_body_jmp_args(b);
                        let n = array_size(jmp_args);
                        // Evaluate all args first, then assign
                        let mut vals: Vec<IrValue> = Vec::with_capacity(n);
                        for i in 0..n {
                            vals.push(self.eval_arg(array_get(jmp_args, i)));
                        }
                        for i in 0..n {
                            let param = array_get(jp_params, i);
                            *self.var_slot(param_var(param)) = vals[i];
                        }
                        b = fn_body_jdecl_body(jp);
                    }
                    FnBodyKind::Unreachable => {
                        return Err("unreachable code".to_string());
                    }
                }
            }
        }

        // -----------------------------------------------------------------------
        // lookup_symbol
        // -----------------------------------------------------------------------

        unsafe fn lookup_symbol(
            &mut self,
            fn_name: *mut LeanObject,
        ) -> Result<SymbolCacheEntry, String> {
            let key = NameKey(fn_name);
            // Check per-interpreter cache
            if let Some(&e) = self.m_symbol_cache.get(&key) {
                return Ok(e);
            }
            // Check the process-wide native symbol cache. The C++ implementation
            // protects this map with a shared_mutex; Rust uses a plain mutex here.
            let native_hit = {
                let _lock = native_symbol_cache_lock();
                let cache = native_symbol_cache();
                cache.0.get(&key).copied()
            };
            if let Some(native) = native_hit {
                let decl = self.get_decl(fn_name)?;
                let e = SymbolCacheEntry {
                    m_decl: decl,
                    m_native: native,
                };
                lean_inc(fn_name);
                self.m_symbol_cache.insert(key, e);
                return Ok(e);
            }
            // Not in global cache; compute
            let decl = self.get_decl(fn_name)?;
            let mut native = NativeSymbolCacheEntry {
                m_addr: ptr::null_mut(),
                m_boxed: false,
            };

            lean_inc(self.m_env);
            lean_inc(fn_name);
            let has_init = {
                let opt = lean_get_init_fn_name_for(self.m_env, fn_name);
                let found = !lean_is_scalar(opt);
                if found {
                    lean_dec(opt);
                }
                found
            };

            if self.m_prefer_native || decl_tag(decl) == DeclKind::Extern || has_init {
                lean_inc(self.m_env);
                lean_inc(fn_name);
                let mangled_obj = lean_get_symbol_stem(self.m_env, fn_name);
                lean_inc(mangled_obj);
                let boxed_mangled_obj = lean_mk_mangled_boxed_name(mangled_obj);
                let boxed_mangled_cstr = lean_string_cstr(boxed_mangled_obj);
                if let Some(p_boxed) = {
                    let p = lookup_symbol_in_cur_exe(boxed_mangled_cstr);
                    if p.is_null() { None } else { Some(p) }
                } {
                    native.m_addr = p_boxed;
                    native.m_boxed = true;
                    lean_dec(boxed_mangled_obj);
                    lean_dec(mangled_obj);
                } else {
                    lean_dec(boxed_mangled_obj);
                    // Check for @[export] override
                    lean_inc(self.m_env);
                    lean_inc(fn_name);
                    let export_opt = lean_get_export_name_for(self.m_env, fn_name);
                    let mangled_cstr = if !lean_is_scalar(export_opt) {
                        // Use the export name as string
                        let export_name = lean_ctor_get_obj(export_opt, 0);
                        lean_inc(export_name);
                        lean_dec(export_opt);
                        // export name is already a string (per get_export_name_for returning name.get_string())
                        lean_dec(mangled_obj);
                        export_name
                    } else {
                        lean_dec(export_opt);
                        mangled_obj
                    };
                    let p = lookup_symbol_in_cur_exe(lean_string_cstr(mangled_cstr));
                    if !p.is_null() {
                        native.m_addr = p;
                    }
                    lean_dec(mangled_cstr);
                }
            }

            let native = {
                let _lock = native_symbol_cache_lock();
                let cache = native_symbol_cache();
                if let Some(&cached) = cache.0.get(&key) {
                    cached
                } else {
                    lean_inc(fn_name);
                    cache.0.insert(NameKey(fn_name), native);
                    native
                }
            };

            let e = SymbolCacheEntry {
                m_decl: decl,
                m_native: native,
            };
            lean_inc(fn_name);
            self.m_symbol_cache.insert(key, e);
            Ok(e)
        }

        // -----------------------------------------------------------------------
        // get_decl
        // -----------------------------------------------------------------------

        unsafe fn get_decl(&self, fn_name: *mut LeanObject) -> Result<*mut LeanObject, String> {
            lean_inc(self.m_env);
            lean_inc(fn_name);
            let opt = lean_ir_find_env_decl(self.m_env, fn_name);
            if lean_is_scalar(opt) {
                // None
                let name_str = lean_name_to_string_for_err(fn_name);
                Err(format!("(interpreter) unknown declaration '{}'", name_str))
            } else {
                // Some(decl)
                let decl = lean_ctor_get_obj(opt, 0);
                lean_inc(decl);
                lean_dec(opt);
                Ok(decl)
            }
        }

        // -----------------------------------------------------------------------
        // load (nullary function / "constant")
        // -----------------------------------------------------------------------

        unsafe fn load(&mut self, fn_name: *mut LeanObject, t: IrType) -> Result<IrValue, String> {
            let key = NameKey(fn_name);
            if let Some(cached) = self.m_constant_cache.get(&key) {
                return Ok(cached.m_val);
            }
            // Check g_init_globals
            {
                let globals = init_globals();
                if let Some(&o) = globals.0.get(&key) {
                    return Ok(if t.is_scalar() {
                        unbox_t(o, t)?
                    } else {
                        IrValue::from_obj(o)
                    });
                }
            }

            let sym = self.lookup_symbol(fn_name)?;
            if !sym.m_native.m_addr.is_null() {
                let addr = sym.m_native.m_addr;
                let v = match t {
                    IrType::Float => IrValue::from_float(*(addr as *const f64)),
                    IrType::Float32 => IrValue::from_float32(*(addr as *const f32)),
                    IrType::UInt8 => IrValue::from_num(*(addr as *const u8) as u64),
                    IrType::UInt16 => IrValue::from_num(*(addr as *const u16) as u64),
                    IrType::UInt32 => IrValue::from_num(*(addr as *const u32) as u64),
                    IrType::UInt64 => IrValue::from_num(*(addr as *const u64)),
                    IrType::USize => IrValue::from_num(*(addr as *const usize) as u64),
                    IrType::Object
                    | IrType::Tagged
                    | IrType::TObject
                    | IrType::Irrelevant
                    | IrType::Void => IrValue::from_obj(*(addr as *const *mut LeanObject)),
                    _ => return Err("load: not implemented yet for Struct/Union".to_string()),
                };
                return Ok(v);
            }

            // Check for [init] attribute
            lean_inc(self.m_env);
            lean_inc(fn_name);
            let init_opt = lean_get_regular_init_fn_name_for(self.m_env, fn_name);
            if !lean_is_scalar(init_opt) {
                lean_dec(init_opt);
                let name_str = lean_name_to_string_for_err(fn_name);
                return Err(format!(
                    "cannot evaluate `[init]` declaration '{}' in the same module",
                    name_str
                ));
            }
            lean_dec(init_opt);

            let old_size = self.m_arg_stack.len();
            self.push_frame(sym.m_decl, old_size);
            let body = decl_fun_body(sym.m_decl)?;
            if fn_body_tag(body) == FnBodyKind::Unreachable {
                self.pop_frame();
                let name_str = lean_name_to_string_for_err(fn_name);
                return Err(format!(
                    "(interpreter) constant '{}' has unreachable body; initializer may not have run",
                    name_str
                ));
            }
            let r = self.eval_body(body)?;
            self.pop_frame();

            let is_scalar = t.is_scalar();
            lean_inc(fn_name);
            self.m_constant_cache.insert(
                NameKey(fn_name),
                ConstantCacheEntry {
                    m_is_scalar: is_scalar,
                    m_val: r,
                },
            );
            Ok(r)
        }

        // -----------------------------------------------------------------------
        // call
        // -----------------------------------------------------------------------

        unsafe fn call(
            &mut self,
            fn_name: *mut LeanObject,
            args: *mut LeanObject,
        ) -> Result<IrValue, String> {
            let old_size = self.m_arg_stack.len();
            let sym = self.lookup_symbol(fn_name)?;
            if !sym.m_native.m_addr.is_null() {
                let n = array_size(args);
                let mut args_buf: Vec<*mut LeanObject> = Vec::with_capacity(n);
                for i in 0..n {
                    let arg = array_get(args, i);
                    let param = decl_params_get(sym.m_decl, i);
                    let ty = param_type(param)?;
                    let boxed = box_t(self.eval_arg(arg), ty)?;
                    if sym.m_native.m_boxed && param_borrow(param) {
                        lean_inc(boxed);
                    }
                    args_buf.push(boxed);
                }
                self.push_frame(sym.m_decl, old_size);
                let o = lean_curry(sym.m_native.m_addr, n as u32, args_buf.as_mut_ptr());
                let ret_t = decl_type_field(sym.m_decl)?;
                let r = if ret_t.is_scalar() {
                    let v = unbox_t(o, ret_t)?;
                    lean_dec(o);
                    v
                } else {
                    IrValue::from_obj(o)
                };
                self.pop_frame();
                Ok(r)
            } else {
                if decl_tag(sym.m_decl) == DeclKind::Extern {
                    let name_str = lean_name_to_string_for_err(fn_name);
                    lean_inc(self.m_env);
                    lean_inc(fn_name);
                    let mangled_obj = lean_get_symbol_stem(self.m_env, fn_name);
                    lean_inc(mangled_obj);
                    let boxed_mangled_obj = lean_mk_mangled_boxed_name(mangled_obj);
                    let boxed_str = lean_string_cstr(boxed_mangled_obj);
                    let mangled_str = lean_string_cstr(mangled_obj);
                    let msg = format!(
                        "Could not find native implementation of external declaration '{}' \
                        (symbols '{}' or '{}').\nFor declarations from `Init`, `Std`, or `Lean`, \
                        you need to set `supportInterpreter := true` in the relevant `lean_exe` \
                        statement in your `lakefile.lean`.",
                        name_str,
                        core::ffi::CStr::from_ptr(boxed_str).to_string_lossy(),
                        core::ffi::CStr::from_ptr(mangled_str).to_string_lossy(),
                    );
                    lean_dec(boxed_mangled_obj);
                    lean_dec(mangled_obj);
                    return Err(msg);
                }
                // Evaluate args in old stack frame
                let n = array_size(args);
                for i in 0..n {
                    let v = self.eval_arg(array_get(args, i));
                    self.m_arg_stack.push(v);
                }
                self.push_frame(sym.m_decl, old_size);
                let body = decl_fun_body(sym.m_decl)?;
                let r = self.eval_body(body)?;
                self.pop_frame();
                Ok(r)
            }
        }

        // -----------------------------------------------------------------------
        // stub_m (closure stub)
        // -----------------------------------------------------------------------

        unsafe fn stub_m(&mut self, args: *mut *mut LeanObject) -> *mut LeanObject {
            let d = *args.add(2);
            let old_size = self.m_arg_stack.len();
            let n = decl_params_size(d);
            for i in 0..n {
                self.m_arg_stack.push(IrValue::from_obj(*args.add(3 + i)));
            }
            self.push_frame(d, old_size);
            let r = match decl_fun_body(d) {
                Ok(body) => match self.eval_body(body) {
                    Ok(v) => v.obj(),
                    Err(e) => {
                        // Convert error to IO error and panic (we're inside a closure)
                        let c_msg = std::ffi::CString::new(e).unwrap_or_default();
                        let s = lean_mk_string(c_msg.as_ptr());
                        let mut fields = [s];
                        let ioe = lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0);
                        lean_io_result_mk_error(ioe)
                    }
                },
                Err(e) => {
                    let c_msg = std::ffi::CString::new(e).unwrap_or_default();
                    let s = lean_mk_string(c_msg.as_ptr());
                    let mut fields = [s];
                    let ioe = lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0);
                    lean_io_result_mk_error(ioe)
                }
            };
            self.pop_frame();
            r
        }

        // -----------------------------------------------------------------------
        // call_boxed
        // -----------------------------------------------------------------------

        unsafe fn call_boxed(
            &mut self,
            fn_name: *mut LeanObject,
            n: usize,
            args: *const *mut LeanObject,
        ) -> Result<*mut LeanObject, String> {
            let sym = self.lookup_symbol(fn_name)?;
            let arity = decl_params_size(sym.m_decl);
            if arity == 0 {
                let t = decl_type_field(sym.m_decl)?;
                let v = self.load(fn_name, t)?;
                let o = box_t(v, t)?;
                if !t.is_scalar() {
                    lean_inc(o);
                }
                let r = if n > 0 {
                    lean_apply_n(o, n as u32, args as *mut *mut LeanObject)
                } else {
                    o
                };
                return Ok(r);
            }
            // Build initial closure
            let cls = if !sym.m_native.m_addr.is_null() {
                lean_alloc_closure(sym.m_native.m_addr, arity as u32, 0)
            } else {
                // Check for boxed IR decl
                lean_inc(self.m_env);
                lean_inc(fn_name);
                let boxed_opt = lean_ir_find_env_decl_boxed(self.m_env, fn_name);
                let d = if !lean_is_scalar(boxed_opt) {
                    let decl = lean_ctor_get_obj(boxed_opt, 0);
                    lean_inc(decl);
                    lean_dec(boxed_opt);
                    decl
                } else {
                    lean_dec(boxed_opt);
                    sym.m_decl
                };
                self.mk_stub_closure(d, 0, ptr::null())
            };
            let r = if n > 0 {
                lean_apply_n(cls, n as u32, args as *mut *mut LeanObject)
            } else {
                cls
            };
            Ok(r)
        }

        // -----------------------------------------------------------------------
        // run_main
        // -----------------------------------------------------------------------

        unsafe fn run_main(&mut self, args: *mut LeanObject) -> Result<u32, String> {
            // Look up "main" decl to determine arity
            let main_name = mk_lean_name_anon("main");
            let d = self.get_decl(main_name)?;
            let params_count = decl_params_size(d);
            lean_dec(d);

            let mut call_args: Vec<*mut LeanObject> = Vec::with_capacity(3);
            if params_count == 2 {
                lean_inc(args);
                call_args.push(args);
            }
            let w = lean_io_mk_world();
            call_args.push(w);

            let w2 = self.call_boxed(main_name, call_args.len(), call_args.as_ptr())?;
            lean_dec(main_name);

            if lean_io_result_is_ok(w2) {
                // Distinguish IO Unit (returns box(0)) from IO UInt32 (returns lean_box(v) on 64-bit)
                // On 64-bit, both UInt32 and Unit are scalar. Check if value != box(0) to detect UInt32 != 0.
                // Actually: for IO Unit the value is always box(0); for IO UInt32 it's lean_box(v).
                // lean_unbox(box(v)) = v, so we can always safely do lean_unbox for both cases.
                let ret_val = lean_io_result_get_value(w2);
                let ret = lean_unbox(ret_val) as u32;
                lean_dec(w2);
                Ok(ret)
            } else {
                lean_io_result_show_error(w2);
                lean_dec(w2);
                Ok(1)
            }
        }

        // -----------------------------------------------------------------------
        // run_init
        // -----------------------------------------------------------------------

        unsafe fn run_init(
            &mut self,
            decl_name: *mut LeanObject,
            init_decl_name: *mut LeanObject,
        ) -> Result<*mut LeanObject, String> {
            let args: [*mut LeanObject; 0] = [];
            let r = self.call_boxed(init_decl_name, 1, args.as_ptr())?;
            if lean_io_result_is_ok(r) {
                let o = lean_io_result_get_value(r);
                lean_inc(o);
                lean_mark_persistent(o);
                lean_dec(r);
                // Store in native slot if possible, else g_init_globals
                let sym = self.lookup_symbol(decl_name)?;
                if !sym.m_native.m_addr.is_null() {
                    *(sym.m_native.m_addr as *mut *mut LeanObject) = o;
                } else {
                    let globals = init_globals();
                    lean_inc(decl_name);
                    globals.0.insert(NameKey(decl_name), o);
                }
                Ok(lean_io_result_mk_ok(lean_box(0)))
            } else {
                Ok(r) // propagate IO error
            }
        }
    }

    impl Drop for Interpreter {
        fn drop(&mut self) {
            unsafe {
                for (_, entry) in &self.m_constant_cache {
                    if !entry.m_is_scalar {
                        lean_dec(entry.m_val.obj());
                    }
                }
                for (_, entry) in &self.m_symbol_cache {
                    lean_dec(entry.m_decl);
                }
            }
        }
    }

    // ---------------------------------------------------------------------------
    // mk_lean_name_anon - create an anonymous (single-component) name
    // ---------------------------------------------------------------------------

    unsafe fn mk_lean_name_anon(s: &str) -> *mut LeanObject {
        let c_s = std::ffi::CString::new(s).unwrap();
        let str_obj = lean_mk_string(c_s.as_ptr());
        lean_name_mk_string(lean_box(0), str_obj)
    }

    // ---------------------------------------------------------------------------
    // with_interpreter
    // ---------------------------------------------------------------------------

    unsafe fn with_interpreter_obj<T, F>(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        fn_name: *mut LeanObject,
        f: F,
    ) -> T
    where
        F: FnOnce(&mut Interpreter) -> T,
    {
        let current = get_interpreter();
        if !current.is_null() && (*current).m_env == env && (*current).m_opts == opts {
            return f(&mut *current);
        }
        // Create new interpreter with scope_trace_env + time_task_guard
        lean_inc(fn_name);
        let _ttg = TimeTaskGuard::new(c"interpretation".as_ptr(), opts, fn_name);
        let _scope = ScopeTraceEnvGuard::new(env, opts);
        let mut interp = Interpreter::new(env, opts);
        let interp_ptr = &mut interp as *mut Interpreter;
        let old = get_interpreter();
        set_interpreter(interp_ptr);
        struct RestoreInterp(*mut Interpreter);
        impl Drop for RestoreInterp {
            fn drop(&mut self) {
                unsafe {
                    set_interpreter(self.0);
                }
            }
        }
        let _restore = RestoreInterp(old);
        f(&mut interp)
    }

    // ---------------------------------------------------------------------------
    // run_boxed
    // ---------------------------------------------------------------------------

    unsafe fn run_boxed(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        fn_name: *mut LeanObject,
        n: usize,
        args: *const *mut LeanObject,
    ) -> Result<*mut LeanObject, String> {
        // Check sorry dep
        lean_inc(env);
        lean_inc(fn_name);
        let sorry_opt = lean_decl_get_sorry_dep(env, fn_name);
        if !lean_is_scalar(sorry_opt) {
            let dep_name = lean_ctor_get_obj(sorry_opt, 0);
            let dep_str = lean_name_to_string_for_err(dep_name);
            lean_dec(sorry_opt);
            return Err(format!(
                "cannot evaluate code because '{}' uses 'sorry' and/or contains errors",
                dep_str
            ));
        }
        lean_dec(sorry_opt);

        with_interpreter_obj(env, opts, fn_name, |interp| {
            interp.call_boxed(fn_name, n, args)
        })
    }

    // ---------------------------------------------------------------------------
    // Stub closures (stub_1_aux through stub_16_aux + stub_m_aux)
    // ---------------------------------------------------------------------------

    unsafe fn stub_m_aux_impl(args: *mut *mut LeanObject) -> *mut LeanObject {
        let env = *args.add(0);
        let opts = *args.add(1);
        let d = *args.add(2);
        let fn_name = decl_fun_id(d);
        with_interpreter_obj(env, opts, fn_name, |interp| interp.stub_m(args))
    }

    unsafe fn stub_1_aux(x1: *mut LeanObject) -> *mut LeanObject {
        let mut args = [x1];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_2_aux(x1: *mut LeanObject, x2: *mut LeanObject) -> *mut LeanObject {
        let mut args = [x1, x2];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_3_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_4_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_5_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_6_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_7_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_8_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7, x8];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_9_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7, x8, x9];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_10_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
        x10: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_11_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
        x10: *mut LeanObject,
        x11: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_12_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
        x10: *mut LeanObject,
        x11: *mut LeanObject,
        x12: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_13_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
        x10: *mut LeanObject,
        x11: *mut LeanObject,
        x12: *mut LeanObject,
        x13: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_14_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
        x10: *mut LeanObject,
        x11: *mut LeanObject,
        x12: *mut LeanObject,
        x13: *mut LeanObject,
        x14: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_15_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
        x10: *mut LeanObject,
        x11: *mut LeanObject,
        x12: *mut LeanObject,
        x13: *mut LeanObject,
        x14: *mut LeanObject,
        x15: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [
            x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
        ];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    unsafe fn stub_16_aux(
        x1: *mut LeanObject,
        x2: *mut LeanObject,
        x3: *mut LeanObject,
        x4: *mut LeanObject,
        x5: *mut LeanObject,
        x6: *mut LeanObject,
        x7: *mut LeanObject,
        x8: *mut LeanObject,
        x9: *mut LeanObject,
        x10: *mut LeanObject,
        x11: *mut LeanObject,
        x12: *mut LeanObject,
        x13: *mut LeanObject,
        x14: *mut LeanObject,
        x15: *mut LeanObject,
        x16: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut args = [
            x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16,
        ];
        stub_m_aux_impl(args.as_mut_ptr())
    }
    // stub_m_aux with varargs via pointer
    unsafe fn stub_m_aux(args: *mut *mut LeanObject) -> *mut LeanObject {
        stub_m_aux_impl(args)
    }

    unsafe fn get_stub(params: u32) -> *mut core::ffi::c_void {
        match params {
            0 => unreachable!("get_stub: params == 0"),
            1 => stub_1_aux as *mut core::ffi::c_void,
            2 => stub_2_aux as *mut core::ffi::c_void,
            3 => stub_3_aux as *mut core::ffi::c_void,
            4 => stub_4_aux as *mut core::ffi::c_void,
            5 => stub_5_aux as *mut core::ffi::c_void,
            6 => stub_6_aux as *mut core::ffi::c_void,
            7 => stub_7_aux as *mut core::ffi::c_void,
            8 => stub_8_aux as *mut core::ffi::c_void,
            9 => stub_9_aux as *mut core::ffi::c_void,
            10 => stub_10_aux as *mut core::ffi::c_void,
            11 => stub_11_aux as *mut core::ffi::c_void,
            12 => stub_12_aux as *mut core::ffi::c_void,
            13 => stub_13_aux as *mut core::ffi::c_void,
            14 => stub_14_aux as *mut core::ffi::c_void,
            15 => stub_15_aux as *mut core::ffi::c_void,
            16 => stub_16_aux as *mut core::ffi::c_void,
            _ => stub_m_aux as *mut core::ffi::c_void,
        }
    }

    // ---------------------------------------------------------------------------
    // Public exported functions
    // ---------------------------------------------------------------------------

    /// initialize_ir_interpreter — called from lib.rs initialize_library_module_body
    #[no_mangle]
    pub unsafe fn initialize_ir_interpreter() {}

    /// finalize_ir_interpreter — called from lib.rs
    #[no_mangle]
    pub unsafe fn finalize_ir_interpreter() {
        // Drop the global caches. OnceLock doesn't support resetting, so just clear contents.
        {
            let _lock = native_symbol_cache_lock();
            if !G_NATIVE_SYMBOL_CACHE.is_null() {
                let _w = unsafe { Box::from_raw(G_NATIVE_SYMBOL_CACHE) };
                G_NATIVE_SYMBOL_CACHE = ptr::null_mut();
            }
        }
        if !G_INIT_GLOBALS.is_null() {
            let mut w = unsafe { Box::from_raw(G_INIT_GLOBALS) };
            G_INIT_GLOBALS = ptr::null_mut();
            let globals = core::mem::take(&mut w.0);
            for (_, o) in globals.into_iter() {
                lean_dec(o);
            }
            drop(w);
        }
        // Decrement the prefer_native name
        let name_obj = G_INTERPRETER_PREFER_NATIVE_NAME.swap(ptr::null_mut(), Ordering::AcqRel);
        if !name_obj.is_null() {
            lean_dec(name_obj);
        }
    }

    /// lean_eval_main (env : Environment) (opts : Options) (args : List String) : BaseIO UInt32
    #[no_mangle]
    pub unsafe fn lean_eval_main(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        args: *mut LeanObject,
    ) -> u32 {
        let main_name = mk_lean_name_anon("main");
        let ret = with_interpreter_obj(env, opts, main_name, |interp| interp.run_main(args));
        lean_dec(main_name);
        match ret {
            Ok(v) => v,
            Err(e) => {
                let c_msg = std::ffi::CString::new(e).unwrap_or_default();
                let s = lean_mk_string(c_msg.as_ptr());
                let mut fields = [s];
                let ioe = lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0);
                let r = lean_io_result_mk_error(ioe);
                lean_io_result_show_error(r);
                lean_dec(r);
                1
            }
        }
    }

    /// lean_eval_const (env : Environment) (opts : Options) (c : Name) : Except String _
    #[no_mangle]
    pub unsafe fn lean_eval_const(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        c: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(c);
        match run_boxed(env, opts, c, 0, ptr::null()) {
            Ok(r) => {
                let mut fields = [r];
                lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0) // Except.ok r
            }
            Err(e) => {
                let c_msg = std::ffi::CString::new(e).unwrap_or_default();
                let s = lean_mk_string(c_msg.as_ptr());
                let mut fields = [s];
                lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0) // Except.error msg
            }
        }
    }

    /// C++ kernel/type_checker bridge for Lean.reduceNat/Lean.reduceBool.
    ///
    /// Returns `Except String Object`; the C++ shim converts the error case
    /// back into a C++ exception to preserve the old `ir::run_boxed_kernel`
    /// contract.
    #[no_mangle]
    pub unsafe fn lean_eval_const_at_kernel_env(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        c: *mut LeanObject,
        n: usize,
        args: *mut *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(env);
        let elab_env = lean_elab_environment_of_kernel_env(env);
        lean_inc(c);
        let result = match run_boxed(elab_env, opts, c, n, args) {
            Ok(r) => {
                let mut fields = [r];
                lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
            }
            Err(e) => {
                let c_msg = std::ffi::CString::new(e).unwrap_or_default();
                let s = lean_mk_string(c_msg.as_ptr());
                let mut fields = [s];
                lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0)
            }
        };
        lean_dec(elab_env);
        result
    }

    /// lean_run_init (env opts decl init_decl io) : IO Unit
    #[no_mangle]
    pub unsafe fn lean_run_init(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        decl: *mut LeanObject,
        init_decl: *mut LeanObject,
        _io: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(decl);
        with_interpreter_obj(env, opts, decl, |interp| {
            lean_inc(decl);
            lean_inc(init_decl);
            match interp.run_init(decl, init_decl) {
                Ok(r) => r,
                Err(e) => lean_io_result_mk_error_msg(&e),
            }
        })
    }

    /// lean_run_mod_init_core (sym : @& String) : IO Bool
    ///
    /// On Unix, uses dlsym(RTLD_DEFAULT, ...) directly.
    /// On Windows, uses EnumProcessModules/GetProcAddress.
    #[no_mangle]
    pub unsafe fn lean_run_mod_init_core(sym: *mut LeanObject) -> *mut LeanObject {
        let sym_cstr = lean_string_cstr(sym);
        let init = lookup_symbol_in_cur_exe(sym_cstr);
        if init.is_null() {
            lean_io_result_mk_ok(lean_box(0)) // Bool.false: symbol not found
        } else {
            let init_fn: unsafe fn(u8) -> *mut LeanObject = core::mem::transmute(init);
            let builtin: u8 = 0;
            let r = init_fn(builtin);
            if lean_io_result_is_ok(r) {
                lean_dec_ref(r);
                lean_io_result_mk_ok(lean_box(1)) // Bool.true: init succeeded
            } else {
                r // propagate IO error from the init function
            }
        }
    }
}
