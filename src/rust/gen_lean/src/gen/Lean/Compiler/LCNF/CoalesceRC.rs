// Lean compiler output
// Module: Lean.Compiler.LCNF.CoalesceRC
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Expr::{l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_coalesceRC___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [99, 111, 97, 108, 101, 115, 99, 101, 82, 99, 0],
    };
static mut l_Lean_Compiler_LCNF_coalesceRC___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_coalesceRC___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_coalesceRC___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_coalesceRC___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9366571167713227299 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_coalesceRC___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_coalesceRC___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_coalesceRC___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun:
            l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___boxed
                as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_coalesceRC___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_coalesceRC___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_coalesceRC___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_coalesceRC___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_coalesceRC: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_coalesceRC___closed__0_value) as *mut crate::leanh::LeanObject,8703323677962721381 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 97, 108, 101, 115, 99, 101, 82, 67, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5710038546531106922 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10149800833096484971 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5142981379341229910 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4693843688127326196 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15175128654572643509 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14594812538085217116 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,910892556010467541 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14084479933085097920 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14356305970805209242 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17048586965816274043 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10677368720312530616 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(
    mut v_a_1037_: *mut crate::leanh::LeanObject,
    mut v_x_1038_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1039_: u8 = 0;
    let mut v_key_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1038_) == 0 {
                    v___x_1039_ = 0;
                    return v___x_1039_;
                } else {
                    v_key_1040_ = crate::leanh::lean_ctor_get(v_x_1038_, 0);
                    v_tail_1041_ = crate::leanh::lean_ctor_get(v_x_1038_, 2);
                    v___x_1042_ = l_Lean_instBEqFVarId_beq(v_key_1040_, v_a_1037_);
                    if v___x_1042_ == 0 {
                        v_x_1038_ = v_tail_1041_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1042_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg___boxed(
    mut v_a_1044_: *mut crate::leanh::LeanObject,
    mut v_x_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1046_: u8 = 0;
    let mut v_r_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1046_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_a_1044_, v_x_1045_);
    crate::leanh::lean_dec(v_x_1045_);
    crate::leanh::lean_dec(v_a_1044_);
    v_r_1047_ = crate::leanh::lean_box((v_res_1046_) as usize);
    return v_r_1047_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(
    mut v_m_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u64 = 0;
    let mut v___x_1053_: u64 = 0;
    let mut v___x_1054_: u64 = 0;
    let mut v_fold_1055_: u64 = 0;
    let mut v___x_1056_: u64 = 0;
    let mut v___x_1057_: u64 = 0;
    let mut v___x_1058_: u64 = 0;
    let mut v___x_1059_: usize = 0;
    let mut v___x_1060_: usize = 0;
    let mut v___x_1061_: usize = 0;
    let mut v___x_1062_: usize = 0;
    let mut v___x_1063_: usize = 0;
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: u8 = 0;
    v_buckets_1050_ = crate::leanh::lean_ctor_get(v_m_1048_, 1);
    v___x_1051_ = lean_array_get_size(v_buckets_1050_);
    v___x_1052_ = l_Lean_instHashableFVarId_hash(v_a_1049_);
    v___x_1053_ = 32u64;
    v___x_1054_ = lean_uint64_shift_right(v___x_1052_, v___x_1053_);
    v_fold_1055_ = lean_uint64_xor(v___x_1052_, v___x_1054_);
    v___x_1056_ = 16u64;
    v___x_1057_ = lean_uint64_shift_right(v_fold_1055_, v___x_1056_);
    v___x_1058_ = lean_uint64_xor(v_fold_1055_, v___x_1057_);
    v___x_1059_ = lean_uint64_to_usize(v___x_1058_);
    v___x_1060_ = lean_usize_of_nat(v___x_1051_);
    v___x_1061_ = 1usize;
    v___x_1062_ = lean_usize_sub(v___x_1060_, v___x_1061_);
    v___x_1063_ = lean_usize_land(v___x_1059_, v___x_1062_);
    v___x_1064_ = lean_array_uget_borrowed(v_buckets_1050_, v___x_1063_);
    v___x_1065_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_a_1049_, v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg___boxed(
    mut v_m_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1068_: u8 = 0;
    let mut v_r_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_m_1066_, v_a_1067_);
    crate::leanh::lean_dec(v_a_1067_);
    crate::leanh::lean_dec_ref(v_m_1066_);
    v_r_1069_ = crate::leanh::lean_box((v_res_1068_) as usize);
    return v_r_1069_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5___lam__0(
    mut v_n_1070_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_x3f_1071_) == 0 {
                    v___x_1076_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1073_ = v___x_1076_;
                    state = 1;
                    continue;
                } else {
                    v_val_1077_ = crate::leanh::lean_ctor_get(v_v_x3f_1071_, 0);
                    v___y_1073_ = v_val_1077_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1074_ = lean_nat_add(v___y_1073_, v_n_1070_);
                v___x_1075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1075_, 0, v___x_1074_);
                return v___x_1075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5___lam__0___boxed(
    mut v_n_1078_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1080_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5___lam__0(v_n_1078_, v_v_x3f_1079_);
    crate::leanh::lean_dec(v_v_x3f_1079_);
    crate::leanh::lean_dec(v_n_1078_);
    return v_res_1080_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5(
    mut v_n_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_x_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: u8 = 0;
    let mut v_tail_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1083_) == 0 {
                    v___x_1084_ = crate::leanh::lean_box(0);
                    v___x_1085_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5___lam__0(v_n_1081_, v___x_1084_);
                    v_val_1086_ = crate::leanh::lean_ctor_get(v___x_1085_, 0);
                    crate::leanh::lean_inc(v_val_1086_);
                    crate::leanh::lean_dec(v___x_1085_);
                    v___x_1087_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1087_, 0, v_a_1082_);
                    crate::leanh::lean_ctor_set(v___x_1087_, 1, v_val_1086_);
                    crate::leanh::lean_ctor_set(v___x_1087_, 2, v_x_1083_);
                    return v___x_1087_;
                } else {
                    v_key_1088_ = crate::leanh::lean_ctor_get(v_x_1083_, 0);
                    v_value_1089_ = crate::leanh::lean_ctor_get(v_x_1083_, 1);
                    v_tail_1090_ = crate::leanh::lean_ctor_get(v_x_1083_, 2);
                    v_isSharedCheck_1105_ = (!crate::leanh::lean_is_exclusive(v_x_1083_)) as u8;
                    if v_isSharedCheck_1105_ == 0 {
                        v___x_1092_ = v_x_1083_;
                        v_isShared_1093_ = v_isSharedCheck_1105_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1090_);
                        crate::leanh::lean_inc(v_value_1089_);
                        crate::leanh::lean_inc(v_key_1088_);
                        crate::leanh::lean_dec(v_x_1083_);
                        v___x_1092_ = crate::leanh::lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1105_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1094_ = l_Lean_instBEqFVarId_beq(v_key_1088_, v_a_1082_);
                if v___x_1094_ == 0 {
                    v_tail_1095_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5(v_n_1081_, v_a_1082_, v_tail_1090_);
                    if v_isShared_1093_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1092_, 2, v_tail_1095_);
                        v___x_1097_ = v___x_1092_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1098_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_key_1088_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_value_1089_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_tail_1095_);
                        v___x_1097_ = v_reuseFailAlloc_1098_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_1088_);
                    v___x_1099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1099_, 0, v_value_1089_);
                    v___x_1100_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5___lam__0(v_n_1081_, v___x_1099_);
                    crate::leanh::lean_dec_ref_known(v___x_1099_, 1);
                    v_val_1101_ = crate::leanh::lean_ctor_get(v___x_1100_, 0);
                    crate::leanh::lean_inc(v_val_1101_);
                    crate::leanh::lean_dec(v___x_1100_);
                    if v_isShared_1093_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1092_, 1, v_val_1101_);
                        crate::leanh::lean_ctor_set(v___x_1092_, 0, v_a_1082_);
                        v___x_1103_ = v___x_1092_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1104_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1082_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_val_1101_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_tail_1090_);
                        v___x_1103_ = v_reuseFailAlloc_1104_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1097_;
            }
            3 => {
                return v___x_1103_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5___boxed(
    mut v_n_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_x_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5(v_n_1106_, v_a_1107_, v_x_1108_);
    crate::leanh::lean_dec(v_n_1106_);
    return v_res_1109_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5_spec__9___redArg(
    mut v_x_1110_: *mut crate::leanh::LeanObject,
    mut v_x_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: u64 = 0;
    let mut v___x_1120_: u64 = 0;
    let mut v___x_1121_: u64 = 0;
    let mut v_fold_1122_: u64 = 0;
    let mut v___x_1123_: u64 = 0;
    let mut v___x_1124_: u64 = 0;
    let mut v___x_1125_: u64 = 0;
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: usize = 0;
    let mut v___x_1128_: usize = 0;
    let mut v___x_1129_: usize = 0;
    let mut v___x_1130_: usize = 0;
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1111_) == 0 {
                    return v_x_1110_;
                } else {
                    v_key_1112_ = crate::leanh::lean_ctor_get(v_x_1111_, 0);
                    v_value_1113_ = crate::leanh::lean_ctor_get(v_x_1111_, 1);
                    v_tail_1114_ = crate::leanh::lean_ctor_get(v_x_1111_, 2);
                    v_isSharedCheck_1137_ = (!crate::leanh::lean_is_exclusive(v_x_1111_)) as u8;
                    if v_isSharedCheck_1137_ == 0 {
                        v___x_1116_ = v_x_1111_;
                        v_isShared_1117_ = v_isSharedCheck_1137_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1114_);
                        crate::leanh::lean_inc(v_value_1113_);
                        crate::leanh::lean_inc(v_key_1112_);
                        crate::leanh::lean_dec(v_x_1111_);
                        v___x_1116_ = crate::leanh::lean_box(0);
                        v_isShared_1117_ = v_isSharedCheck_1137_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1118_ = lean_array_get_size(v_x_1110_);
                v___x_1119_ = l_Lean_instHashableFVarId_hash(v_key_1112_);
                v___x_1120_ = 32u64;
                v___x_1121_ = lean_uint64_shift_right(v___x_1119_, v___x_1120_);
                v_fold_1122_ = lean_uint64_xor(v___x_1119_, v___x_1121_);
                v___x_1123_ = 16u64;
                v___x_1124_ = lean_uint64_shift_right(v_fold_1122_, v___x_1123_);
                v___x_1125_ = lean_uint64_xor(v_fold_1122_, v___x_1124_);
                v___x_1126_ = lean_uint64_to_usize(v___x_1125_);
                v___x_1127_ = lean_usize_of_nat(v___x_1118_);
                v___x_1128_ = 1usize;
                v___x_1129_ = lean_usize_sub(v___x_1127_, v___x_1128_);
                v___x_1130_ = lean_usize_land(v___x_1126_, v___x_1129_);
                v___x_1131_ = lean_array_uget_borrowed(v_x_1110_, v___x_1130_);
                crate::leanh::lean_inc(v___x_1131_);
                if v_isShared_1117_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1116_, 2, v___x_1131_);
                    v___x_1133_ = v___x_1116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_key_1112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_value_1113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 2, v___x_1131_);
                    v___x_1133_ = v_reuseFailAlloc_1136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1134_ = lean_array_uset(v_x_1110_, v___x_1130_, v___x_1133_);
                v_x_1110_ = v___x_1134_;
                v_x_1111_ = v_tail_1114_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5___redArg(
    mut v_i_1138_: *mut crate::leanh::LeanObject,
    mut v_source_1139_: *mut crate::leanh::LeanObject,
    mut v_target_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: u8 = 0;
    let mut v_es_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1141_ = lean_array_get_size(v_source_1139_);
                v___x_1142_ = lean_nat_dec_lt(v_i_1138_, v___x_1141_);
                if v___x_1142_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1139_);
                    crate::leanh::lean_dec(v_i_1138_);
                    return v_target_1140_;
                } else {
                    v_es_1143_ = lean_array_fget(v_source_1139_, v_i_1138_);
                    v___x_1144_ = crate::leanh::lean_box(0);
                    v_source_1145_ = lean_array_fset(v_source_1139_, v_i_1138_, v___x_1144_);
                    v_target_1146_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5_spec__9___redArg(v_target_1140_, v_es_1143_);
                    v___x_1147_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1148_ = lean_nat_add(v_i_1138_, v___x_1147_);
                    crate::leanh::lean_dec(v_i_1138_);
                    v_i_1138_ = v___x_1148_;
                    v_source_1139_ = v_source_1145_;
                    v_target_1140_ = v_target_1146_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4___redArg(
    mut v_data_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1151_ = lean_array_get_size(v_data_1150_);
    v___x_1152_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1153_ = lean_nat_mul(v___x_1151_, v___x_1152_);
    v___x_1154_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1155_ = crate::leanh::lean_box(0);
    v___x_1156_ = lean_mk_array(v_nbuckets_1153_, v___x_1155_);
    v___x_1157_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5___redArg(v___x_1154_, v_data_1150_, v___x_1156_);
    return v___x_1157_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(
    mut v_n_1158_: *mut crate::leanh::LeanObject,
    mut v_m_1159_: *mut crate::leanh::LeanObject,
    mut v_a_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u64 = 0;
    let mut v___x_1168_: u64 = 0;
    let mut v___x_1169_: u64 = 0;
    let mut v_fold_1170_: u64 = 0;
    let mut v___x_1171_: u64 = 0;
    let mut v___x_1172_: u64 = 0;
    let mut v___x_1173_: u64 = 0;
    let mut v___x_1174_: usize = 0;
    let mut v___x_1175_: usize = 0;
    let mut v___x_1176_: usize = 0;
    let mut v___x_1177_: usize = 0;
    let mut v___x_1178_: usize = 0;
    let mut v_bkt_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u8 = 0;
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v_val_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1161_ = crate::leanh::lean_ctor_get(v_m_1159_, 0);
                v_buckets_1162_ = crate::leanh::lean_ctor_get(v_m_1159_, 1);
                v_isSharedCheck_1210_ = (!crate::leanh::lean_is_exclusive(v_m_1159_)) as u8;
                if v_isSharedCheck_1210_ == 0 {
                    v___x_1164_ = v_m_1159_;
                    v_isShared_1165_ = v_isSharedCheck_1210_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1162_);
                    crate::leanh::lean_inc(v_size_1161_);
                    crate::leanh::lean_dec(v_m_1159_);
                    v___x_1164_ = crate::leanh::lean_box(0);
                    v_isShared_1165_ = v_isSharedCheck_1210_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1166_ = lean_array_get_size(v_buckets_1162_);
                v___x_1167_ = l_Lean_instHashableFVarId_hash(v_a_1160_);
                v___x_1168_ = 32u64;
                v___x_1169_ = lean_uint64_shift_right(v___x_1167_, v___x_1168_);
                v_fold_1170_ = lean_uint64_xor(v___x_1167_, v___x_1169_);
                v___x_1171_ = 16u64;
                v___x_1172_ = lean_uint64_shift_right(v_fold_1170_, v___x_1171_);
                v___x_1173_ = lean_uint64_xor(v_fold_1170_, v___x_1172_);
                v___x_1174_ = lean_uint64_to_usize(v___x_1173_);
                v___x_1175_ = lean_usize_of_nat(v___x_1166_);
                v___x_1176_ = 1usize;
                v___x_1177_ = lean_usize_sub(v___x_1175_, v___x_1176_);
                v___x_1178_ = lean_usize_land(v___x_1174_, v___x_1177_);
                v_bkt_1179_ = lean_array_uget_borrowed(v_buckets_1162_, v___x_1178_);
                v___x_1180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_a_1160_, v_bkt_1179_);
                if v___x_1180_ == 0 {
                    v___x_1181_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1182_ = lean_nat_add(v_size_1161_, v___x_1181_);
                    crate::leanh::lean_dec(v_size_1161_);
                    crate::leanh::lean_inc(v_bkt_1179_);
                    v___x_1183_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1183_, 0, v_a_1160_);
                    crate::leanh::lean_ctor_set(v___x_1183_, 1, v_n_1158_);
                    crate::leanh::lean_ctor_set(v___x_1183_, 2, v_bkt_1179_);
                    v_buckets_x27_1184_ =
                        lean_array_uset(v_buckets_1162_, v___x_1178_, v___x_1183_);
                    v___x_1185_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1186_ = lean_nat_mul(v_size_x27_1182_, v___x_1185_);
                    v___x_1187_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1188_ = lean_nat_div(v___x_1186_, v___x_1187_);
                    crate::leanh::lean_dec(v___x_1186_);
                    v___x_1189_ = lean_array_get_size(v_buckets_x27_1184_);
                    v___x_1190_ = lean_nat_dec_le(v___x_1188_, v___x_1189_);
                    crate::leanh::lean_dec(v___x_1188_);
                    if v___x_1190_ == 0 {
                        v_val_1191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4___redArg(v_buckets_x27_1184_);
                        if v_isShared_1165_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1164_, 1, v_val_1191_);
                            crate::leanh::lean_ctor_set(v___x_1164_, 0, v_size_x27_1182_);
                            v___x_1193_ = v___x_1164_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1194_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1194_,
                                0,
                                v_size_x27_1182_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_val_1191_);
                            v___x_1193_ = v_reuseFailAlloc_1194_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1165_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1164_, 1, v_buckets_x27_1184_);
                            crate::leanh::lean_ctor_set(v___x_1164_, 0, v_size_x27_1182_);
                            v___x_1196_ = v___x_1164_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1197_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1197_,
                                0,
                                v_size_x27_1182_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1197_,
                                1,
                                v_buckets_x27_1184_,
                            );
                            v___x_1196_ = v_reuseFailAlloc_1197_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1179_);
                    v___x_1198_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1199_ =
                        lean_array_uset(v_buckets_1162_, v___x_1178_, v___x_1198_);
                    crate::leanh::lean_inc(v_a_1160_);
                    v_bkt_x27_1200_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__5(v_n_1158_, v_a_1160_, v_bkt_1179_);
                    crate::leanh::lean_dec(v_n_1158_);
                    v___x_1207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_a_1160_, v_bkt_x27_1200_);
                    crate::leanh::lean_dec(v_a_1160_);
                    if v___x_1207_ == 0 {
                        v___x_1208_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1209_ = lean_nat_sub(v_size_1161_, v___x_1208_);
                        crate::leanh::lean_dec(v_size_1161_);
                        v___y_1202_ = v___x_1209_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1202_ = v_size_1161_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1193_;
            }
            3 => {
                return v___x_1196_;
            }
            4 => {
                v___x_1203_ = lean_array_uset(v_buckets_x27_1199_, v___x_1178_, v_bkt_x27_1200_);
                if v_isShared_1165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1164_, 1, v___x_1203_);
                    crate::leanh::lean_ctor_set(v___x_1164_, 0, v___y_1202_);
                    v___x_1205_ = v___x_1164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___y_1202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1203_);
                    v___x_1205_ = v_reuseFailAlloc_1206_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(
    mut v_m_1211_: *mut crate::leanh::LeanObject,
    mut v_a_1212_: *mut crate::leanh::LeanObject,
    mut v_b_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u64 = 0;
    let mut v___x_1218_: u64 = 0;
    let mut v___x_1219_: u64 = 0;
    let mut v_fold_1220_: u64 = 0;
    let mut v___x_1221_: u64 = 0;
    let mut v___x_1222_: u64 = 0;
    let mut v___x_1223_: u64 = 0;
    let mut v___x_1224_: usize = 0;
    let mut v___x_1225_: usize = 0;
    let mut v___x_1226_: usize = 0;
    let mut v___x_1227_: usize = 0;
    let mut v___x_1228_: usize = 0;
    let mut v_bkt_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: u8 = 0;
    let mut v_val_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v_unused_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1214_ = crate::leanh::lean_ctor_get(v_m_1211_, 0);
                v_buckets_1215_ = crate::leanh::lean_ctor_get(v_m_1211_, 1);
                v___x_1216_ = lean_array_get_size(v_buckets_1215_);
                v___x_1217_ = l_Lean_instHashableFVarId_hash(v_a_1212_);
                v___x_1218_ = 32u64;
                v___x_1219_ = lean_uint64_shift_right(v___x_1217_, v___x_1218_);
                v_fold_1220_ = lean_uint64_xor(v___x_1217_, v___x_1219_);
                v___x_1221_ = 16u64;
                v___x_1222_ = lean_uint64_shift_right(v_fold_1220_, v___x_1221_);
                v___x_1223_ = lean_uint64_xor(v_fold_1220_, v___x_1222_);
                v___x_1224_ = lean_uint64_to_usize(v___x_1223_);
                v___x_1225_ = lean_usize_of_nat(v___x_1216_);
                v___x_1226_ = 1usize;
                v___x_1227_ = lean_usize_sub(v___x_1225_, v___x_1226_);
                v___x_1228_ = lean_usize_land(v___x_1224_, v___x_1227_);
                v_bkt_1229_ = lean_array_uget_borrowed(v_buckets_1215_, v___x_1228_);
                v___x_1230_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_a_1212_, v_bkt_1229_);
                if v___x_1230_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1215_);
                    crate::leanh::lean_inc(v_size_1214_);
                    v_isSharedCheck_1251_ = (!crate::leanh::lean_is_exclusive(v_m_1211_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v_unused_1252_ = crate::leanh::lean_ctor_get(v_m_1211_, 1);
                        crate::leanh::lean_dec(v_unused_1252_);
                        v_unused_1253_ = crate::leanh::lean_ctor_get(v_m_1211_, 0);
                        crate::leanh::lean_dec(v_unused_1253_);
                        v___x_1232_ = v_m_1211_;
                        v_isShared_1233_ = v_isSharedCheck_1251_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1211_);
                        v___x_1232_ = crate::leanh::lean_box(0);
                        v_isShared_1233_ = v_isSharedCheck_1251_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1213_);
                    crate::leanh::lean_dec(v_a_1212_);
                    return v_m_1211_;
                }
            }
            1 => {
                v___x_1234_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1235_ = lean_nat_add(v_size_1214_, v___x_1234_);
                crate::leanh::lean_dec(v_size_1214_);
                crate::leanh::lean_inc(v_bkt_1229_);
                v___x_1236_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1236_, 0, v_a_1212_);
                crate::leanh::lean_ctor_set(v___x_1236_, 1, v_b_1213_);
                crate::leanh::lean_ctor_set(v___x_1236_, 2, v_bkt_1229_);
                v_buckets_x27_1237_ = lean_array_uset(v_buckets_1215_, v___x_1228_, v___x_1236_);
                v___x_1238_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1239_ = lean_nat_mul(v_size_x27_1235_, v___x_1238_);
                v___x_1240_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1241_ = lean_nat_div(v___x_1239_, v___x_1240_);
                crate::leanh::lean_dec(v___x_1239_);
                v___x_1242_ = lean_array_get_size(v_buckets_x27_1237_);
                v___x_1243_ = lean_nat_dec_le(v___x_1241_, v___x_1242_);
                crate::leanh::lean_dec(v___x_1241_);
                if v___x_1243_ == 0 {
                    v_val_1244_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4___redArg(v_buckets_x27_1237_);
                    if v_isShared_1233_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1232_, 1, v_val_1244_);
                        crate::leanh::lean_ctor_set(v___x_1232_, 0, v_size_x27_1235_);
                        v___x_1246_ = v___x_1232_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_size_x27_1235_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_val_1244_);
                        v___x_1246_ = v_reuseFailAlloc_1247_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1233_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1232_, 1, v_buckets_x27_1237_);
                        crate::leanh::lean_ctor_set(v___x_1232_, 0, v_size_x27_1235_);
                        v___x_1249_ = v___x_1232_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_size_x27_1235_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_buckets_x27_1237_);
                        v___x_1249_ = v_reuseFailAlloc_1250_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1246_;
            }
            3 => {
                return v___x_1249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7_spec__9(
    mut v_msg_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1256_ = lean_panic_fn_borrowed(v___x_1255_, v_msg_1254_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__2;
    v___x_1261_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1262_ = crate::leanh::lean_unsigned_to_nat(163);
    v___x_1263_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__1;
    v___x_1264_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__0;
    v___x_1265_ = l_mkPanicMessageWithDecl(
        v___x_1264_,
        v___x_1263_,
        v___x_1262_,
        v___x_1261_,
        v___x_1260_,
    );
    return v___x_1265_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7(
    mut v_a_1266_: *mut crate::leanh::LeanObject,
    mut v_x_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1267_) == 0 {
                    v___x_1268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___closed__3);
                    v___x_1269_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7_spec__9(v___x_1268_);
                    return v___x_1269_;
                } else {
                    v_key_1270_ = crate::leanh::lean_ctor_get(v_x_1267_, 0);
                    v_value_1271_ = crate::leanh::lean_ctor_get(v_x_1267_, 1);
                    v_tail_1272_ = crate::leanh::lean_ctor_get(v_x_1267_, 2);
                    v___x_1273_ = l_Lean_instBEqFVarId_beq(v_key_1270_, v_a_1266_);
                    if v___x_1273_ == 0 {
                        v_x_1267_ = v_tail_1272_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1271_);
                        return v_value_1271_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7___boxed(
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_x_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1277_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7(v_a_1275_, v_x_1276_);
    crate::leanh::lean_dec(v_x_1276_);
    crate::leanh::lean_dec(v_a_1275_);
    return v_res_1277_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(
    mut v_m_1278_: *mut crate::leanh::LeanObject,
    mut v_a_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: u64 = 0;
    let mut v___x_1283_: u64 = 0;
    let mut v___x_1284_: u64 = 0;
    let mut v_fold_1285_: u64 = 0;
    let mut v___x_1286_: u64 = 0;
    let mut v___x_1287_: u64 = 0;
    let mut v___x_1288_: u64 = 0;
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: usize = 0;
    let mut v___x_1291_: usize = 0;
    let mut v___x_1292_: usize = 0;
    let mut v___x_1293_: usize = 0;
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1280_ = crate::leanh::lean_ctor_get(v_m_1278_, 1);
    v___x_1281_ = lean_array_get_size(v_buckets_1280_);
    v___x_1282_ = l_Lean_instHashableFVarId_hash(v_a_1279_);
    v___x_1283_ = 32u64;
    v___x_1284_ = lean_uint64_shift_right(v___x_1282_, v___x_1283_);
    v_fold_1285_ = lean_uint64_xor(v___x_1282_, v___x_1284_);
    v___x_1286_ = 16u64;
    v___x_1287_ = lean_uint64_shift_right(v_fold_1285_, v___x_1286_);
    v___x_1288_ = lean_uint64_xor(v_fold_1285_, v___x_1287_);
    v___x_1289_ = lean_uint64_to_usize(v___x_1288_);
    v___x_1290_ = lean_usize_of_nat(v___x_1281_);
    v___x_1291_ = 1usize;
    v___x_1292_ = lean_usize_sub(v___x_1290_, v___x_1291_);
    v___x_1293_ = lean_usize_land(v___x_1289_, v___x_1292_);
    v___x_1294_ = lean_array_uget_borrowed(v_buckets_1280_, v___x_1293_);
    v___x_1295_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3_spec__7(v_a_1279_, v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3___boxed(
    mut v_m_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(v_m_1296_, v_a_1297_);
    crate::leanh::lean_dec(v_a_1297_);
    crate::leanh::lean_dec_ref(v_m_1296_);
    return v_res_1298_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(
    mut v_alt_1299_: *mut crate::leanh::LeanObject,
    mut v_f_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1313_: u8 = 0;
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut v_a_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1322_: u8 = 0;
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_code_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_alt_1299_) {
                0 => {
                    v_code_1327_ = crate::leanh::lean_ctor_get(v_alt_1299_, 2);
                    crate::leanh::lean_inc_ref(v_code_1327_);
                    v___y_1308_ = v_code_1327_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_1328_ = crate::leanh::lean_ctor_get(v_alt_1299_, 1);
                    crate::leanh::lean_inc_ref(v_code_1328_);
                    v___y_1308_ = v_code_1328_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_1329_ = crate::leanh::lean_ctor_get(v_alt_1299_, 0);
                    crate::leanh::lean_inc_ref(v_code_1329_);
                    v___y_1308_ = v_code_1329_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                crate::leanh::lean_inc(v___y_1305_);
                crate::leanh::lean_inc_ref(v___y_1304_);
                crate::leanh::lean_inc(v___y_1303_);
                crate::leanh::lean_inc_ref(v___y_1302_);
                crate::leanh::lean_inc(v___y_1301_);
                v___x_1309_ = crate::leanh::lean_apply_7(
                    v_f_1300_,
                    v___y_1308_,
                    v___y_1301_,
                    v___y_1302_,
                    v___y_1303_,
                    v___y_1304_,
                    v___y_1305_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1309_) == 0 {
                    v_a_1310_ = crate::leanh::lean_ctor_get(v___x_1309_, 0);
                    v_isSharedCheck_1318_ = (!crate::leanh::lean_is_exclusive(v___x_1309_)) as u8;
                    if v_isSharedCheck_1318_ == 0 {
                        v___x_1312_ = v___x_1309_;
                        v_isShared_1313_ = v_isSharedCheck_1318_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1310_);
                        crate::leanh::lean_dec(v___x_1309_);
                        v___x_1312_ = crate::leanh::lean_box(0);
                        v_isShared_1313_ = v_isSharedCheck_1318_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_alt_1299_);
                    v_a_1319_ = crate::leanh::lean_ctor_get(v___x_1309_, 0);
                    v_isSharedCheck_1326_ = (!crate::leanh::lean_is_exclusive(v___x_1309_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v___x_1321_ = v___x_1309_;
                        v_isShared_1322_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1319_);
                        crate::leanh::lean_dec(v___x_1309_);
                        v___x_1321_ = crate::leanh::lean_box(0);
                        v_isShared_1322_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1314_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1299_, v_a_1310_);
                if v_isShared_1313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1312_, 0, v___x_1314_);
                    v___x_1316_ = v___x_1312_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1317_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
                    v___x_1316_ = v_reuseFailAlloc_1317_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1316_;
            }
            4 => {
                if v_isShared_1322_ == 0 {
                    v___x_1324_ = v___x_1321_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
                    v___x_1324_ = v_reuseFailAlloc_1325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg___boxed(
    mut v_alt_1330_: *mut crate::leanh::LeanObject,
    mut v_f_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1338_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(v_alt_1330_, v_f_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
    crate::leanh::lean_dec(v___y_1336_);
    crate::leanh::lean_dec_ref(v___y_1335_);
    crate::leanh::lean_dec(v___y_1334_);
    crate::leanh::lean_dec_ref(v___y_1333_);
    crate::leanh::lean_dec(v___y_1332_);
    return v_res_1338_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = crate::leanh::lean_box(0);
    v___x_1340_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1341_ = lean_mk_array(v___x_1340_, v___x_1339_);
    return v___x_1341_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0_once), _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__0);
    v___x_1343_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1344_, 0, v___x_1343_);
    crate::leanh::lean_ctor_set(v___x_1344_, 1, v___x_1342_);
    return v___x_1344_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1_once), _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__1);
    v___x_1346_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1346_, 0, v___x_1345_);
    crate::leanh::lean_ctor_set(v___x_1346_, 1, v___x_1345_);
    crate::leanh::lean_ctor_set(v___x_1346_, 2, v___x_1345_);
    crate::leanh::lean_ctor_set(v___x_1346_, 3, v___x_1345_);
    return v___x_1346_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0___boxed(
    mut v_x_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
    mut v___y_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0(v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
    crate::leanh::lean_dec(v___y_1352_);
    crate::leanh::lean_dec_ref(v___y_1351_);
    crate::leanh::lean_dec(v___y_1350_);
    crate::leanh::lean_dec_ref(v___y_1349_);
    crate::leanh::lean_dec(v___y_1348_);
    return v_res_1354_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1(
    mut v_i_1355_: *mut crate::leanh::LeanObject,
    mut v_as_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: usize = 0;
    let mut v___x_1371_: usize = 0;
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1363_ = lean_array_get_size(v_as_1356_);
                v___x_1364_ = lean_nat_dec_lt(v_i_1355_, v___x_1363_);
                if v___x_1364_ == 0 {
                    crate::leanh::lean_dec(v_i_1355_);
                    v___x_1365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1365_, 0, v_as_1356_);
                    return v___x_1365_;
                } else {
                    v___f_1366_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0___boxed as *mut core::ffi::c_void, 7, 0);
                    v_a_1367_ = lean_array_fget_borrowed(v_as_1356_, v_i_1355_);
                    crate::leanh::lean_inc(v_a_1367_);
                    v___x_1368_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(v_a_1367_, v___f_1366_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
                    if crate::leanh::lean_obj_tag(v___x_1368_) == 0 {
                        v_a_1369_ = crate::leanh::lean_ctor_get(v___x_1368_, 0);
                        crate::leanh::lean_inc(v_a_1369_);
                        crate::leanh::lean_dec_ref_known(v___x_1368_, 1);
                        v___x_1370_ = lean_ptr_addr(v_a_1367_);
                        v___x_1371_ = lean_ptr_addr(v_a_1369_);
                        v___x_1372_ = lean_usize_dec_eq(v___x_1370_, v___x_1371_);
                        if v___x_1372_ == 0 {
                            v___x_1373_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1374_ = lean_nat_add(v_i_1355_, v___x_1373_);
                            v___x_1375_ = lean_array_fset(v_as_1356_, v_i_1355_, v_a_1369_);
                            crate::leanh::lean_dec(v_i_1355_);
                            v_i_1355_ = v___x_1374_;
                            v_as_1356_ = v___x_1375_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1369_);
                            v___x_1377_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1378_ = lean_nat_add(v_i_1355_, v___x_1377_);
                            crate::leanh::lean_dec(v_i_1355_);
                            v_i_1355_ = v___x_1378_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_1356_);
                        crate::leanh::lean_dec(v_i_1355_);
                        v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1368_, 0);
                        v_isSharedCheck_1387_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1368_)) as u8;
                        if v_isSharedCheck_1387_ == 0 {
                            v___x_1382_ = v___x_1368_;
                            v_isShared_1383_ = v_isSharedCheck_1387_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1380_);
                            crate::leanh::lean_dec(v___x_1368_);
                            v___x_1382_ = crate::leanh::lean_box(0);
                            v_isShared_1383_ = v_isSharedCheck_1387_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1383_ == 0 {
                    v___x_1385_ = v___x_1382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
                    v___x_1385_ = v_reuseFailAlloc_1386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(
    mut v_code_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: usize = 0;
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_unused_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_decl_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___y_1437_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1440_: u8 = 0;
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_unused_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: usize = 0;
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: usize = 0;
    let mut v___x_1457_: usize = 0;
    let mut v___x_1458_: u8 = 0;
    let mut v_isSharedCheck_1459_: u8 = 0;
    let mut v_a_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1467_: u8 = 0;
    let mut v_cases_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1482_: usize = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v_unused_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut v_a_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1506_: u8 = 0;
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_fvarId_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_unused_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_fvarId_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1551_: usize = 0;
    let mut v___x_1552_: usize = 0;
    let mut v___x_1553_: u8 = 0;
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v_unused_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_fvarId_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: usize = 0;
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_unused_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1605_: u8 = 0;
    let mut v_fvarId_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: usize = 0;
    let mut v___x_1615_: usize = 0;
    let mut v___x_1616_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_unused_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_fvarId_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1636_: u8 = 0;
    let mut v_persistent_1637_: u8 = 0;
    let mut v_k_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incTotal_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decTotal_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incAccum_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decPlaced_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incTotal_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decTotal_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incAccum_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decPlaced_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incTotal_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incAccum_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v_reuseFailAlloc_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut v_fvarId_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1694_: u8 = 0;
    let mut v_persistent_1695_: u8 = 0;
    let mut v_objs_x3f_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incTotal_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decTotal_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incAccum_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decPlaced_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decTotal_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decPlaced_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incTotal_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decTotal_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_incAccum_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decPlaced_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_reuseFailAlloc_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_fvarId_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1757_: u8 = 0;
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_unused_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_1388_) {
                0 => {
                    v_decl_1395_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_k_1396_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    crate::leanh::lean_inc_ref(v_k_1396_);
                    v___x_1397_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1396_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                    if crate::leanh::lean_obj_tag(v___x_1397_) == 0 {
                        v_a_1398_ = crate::leanh::lean_ctor_get(v___x_1397_, 0);
                        v_isSharedCheck_1420_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1397_)) as u8;
                        if v_isSharedCheck_1420_ == 0 {
                            v___x_1400_ = v___x_1397_;
                            v_isShared_1401_ = v_isSharedCheck_1420_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1398_);
                            crate::leanh::lean_dec(v___x_1397_);
                            v___x_1400_ = crate::leanh::lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1420_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1388_, 2);
                        return v___x_1397_;
                    }
                }
                2 => {
                    v_decl_1421_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_k_1422_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    v_params_1423_ = crate::leanh::lean_ctor_get(v_decl_1421_, 2);
                    v_type_1424_ = crate::leanh::lean_ctor_get(v_decl_1421_, 3);
                    v_value_1425_ = crate::leanh::lean_ctor_get(v_decl_1421_, 4);
                    crate::leanh::lean_inc_ref(v_value_1425_);
                    v___x_1426_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(v_value_1425_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                    if crate::leanh::lean_obj_tag(v___x_1426_) == 0 {
                        v_a_1427_ = crate::leanh::lean_ctor_get(v___x_1426_, 0);
                        crate::leanh::lean_inc(v_a_1427_);
                        crate::leanh::lean_dec_ref_known(v___x_1426_, 1);
                        v___x_1428_ = 1;
                        crate::leanh::lean_inc_ref(v_params_1423_);
                        crate::leanh::lean_inc_ref(v_type_1424_);
                        crate::leanh::lean_inc_ref(v_decl_1421_);
                        v___x_1429_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1428_, v_decl_1421_, v_type_1424_, v_params_1423_, v_a_1427_, v_a_1391_);
                        if crate::leanh::lean_obj_tag(v___x_1429_) == 0 {
                            v_a_1430_ = crate::leanh::lean_ctor_get(v___x_1429_, 0);
                            crate::leanh::lean_inc(v_a_1430_);
                            crate::leanh::lean_dec_ref_known(v___x_1429_, 1);
                            crate::leanh::lean_inc_ref(v_k_1422_);
                            v___x_1431_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1422_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                            if crate::leanh::lean_obj_tag(v___x_1431_) == 0 {
                                v_a_1432_ = crate::leanh::lean_ctor_get(v___x_1431_, 0);
                                v_isSharedCheck_1459_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1431_)) as u8;
                                if v_isSharedCheck_1459_ == 0 {
                                    v___x_1434_ = v___x_1431_;
                                    v_isShared_1435_ = v_isSharedCheck_1459_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1432_);
                                    crate::leanh::lean_dec(v___x_1431_);
                                    v___x_1434_ = crate::leanh::lean_box(0);
                                    v_isShared_1435_ = v_isSharedCheck_1459_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1430_);
                                crate::leanh::lean_dec_ref_known(v_code_1388_, 2);
                                return v___x_1431_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1388_, 2);
                            v_a_1460_ = crate::leanh::lean_ctor_get(v___x_1429_, 0);
                            v_isSharedCheck_1467_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1429_)) as u8;
                            if v_isSharedCheck_1467_ == 0 {
                                v___x_1462_ = v___x_1429_;
                                v_isShared_1463_ = v_isSharedCheck_1467_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1460_);
                                crate::leanh::lean_dec(v___x_1429_);
                                v___x_1462_ = crate::leanh::lean_box(0);
                                v_isShared_1463_ = v_isSharedCheck_1467_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1388_, 2);
                        return v___x_1426_;
                    }
                }
                4 => {
                    v_cases_1468_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    crate::leanh::lean_inc_ref(v_cases_1468_);
                    v_typeName_1469_ = crate::leanh::lean_ctor_get(v_cases_1468_, 0);
                    v_resultType_1470_ = crate::leanh::lean_ctor_get(v_cases_1468_, 1);
                    v_discr_1471_ = crate::leanh::lean_ctor_get(v_cases_1468_, 2);
                    v_alts_1472_ = crate::leanh::lean_ctor_get(v_cases_1468_, 3);
                    v_isSharedCheck_1511_ = (!crate::leanh::lean_is_exclusive(v_cases_1468_)) as u8;
                    if v_isSharedCheck_1511_ == 0 {
                        v___x_1474_ = v_cases_1468_;
                        v_isShared_1475_ = v_isSharedCheck_1511_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_1472_);
                        crate::leanh::lean_inc(v_discr_1471_);
                        crate::leanh::lean_inc(v_resultType_1470_);
                        crate::leanh::lean_inc(v_typeName_1469_);
                        crate::leanh::lean_dec(v_cases_1468_);
                        v___x_1474_ = crate::leanh::lean_box(0);
                        v_isShared_1475_ = v_isSharedCheck_1511_;
                        state = 14;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_1512_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_i_1513_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    v_y_1514_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                    v_k_1515_ = crate::leanh::lean_ctor_get(v_code_1388_, 3);
                    crate::leanh::lean_inc_ref(v_k_1515_);
                    v___x_1516_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1515_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                    if crate::leanh::lean_obj_tag(v___x_1516_) == 0 {
                        v_a_1517_ = crate::leanh::lean_ctor_get(v___x_1516_, 0);
                        v_isSharedCheck_1541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1516_)) as u8;
                        if v_isSharedCheck_1541_ == 0 {
                            v___x_1519_ = v___x_1516_;
                            v_isShared_1520_ = v_isSharedCheck_1541_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1517_);
                            crate::leanh::lean_dec(v___x_1516_);
                            v___x_1519_ = crate::leanh::lean_box(0);
                            v_isShared_1520_ = v_isSharedCheck_1541_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1388_, 4);
                        return v___x_1516_;
                    }
                }
                8 => {
                    v_fvarId_1542_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_i_1543_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    v_y_1544_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                    v_k_1545_ = crate::leanh::lean_ctor_get(v_code_1388_, 3);
                    crate::leanh::lean_inc_ref(v_k_1545_);
                    v___x_1546_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1545_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                    if crate::leanh::lean_obj_tag(v___x_1546_) == 0 {
                        v_a_1547_ = crate::leanh::lean_ctor_get(v___x_1546_, 0);
                        v_isSharedCheck_1571_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1546_)) as u8;
                        if v_isSharedCheck_1571_ == 0 {
                            v___x_1549_ = v___x_1546_;
                            v_isShared_1550_ = v_isSharedCheck_1571_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1547_);
                            crate::leanh::lean_dec(v___x_1546_);
                            v___x_1549_ = crate::leanh::lean_box(0);
                            v_isShared_1550_ = v_isSharedCheck_1571_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1388_, 4);
                        return v___x_1546_;
                    }
                }
                9 => {
                    v_fvarId_1572_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_i_1573_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    v_offset_1574_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                    v_y_1575_ = crate::leanh::lean_ctor_get(v_code_1388_, 3);
                    v_ty_1576_ = crate::leanh::lean_ctor_get(v_code_1388_, 4);
                    v_k_1577_ = crate::leanh::lean_ctor_get(v_code_1388_, 5);
                    crate::leanh::lean_inc_ref(v_k_1577_);
                    v___x_1578_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1577_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                    if crate::leanh::lean_obj_tag(v___x_1578_) == 0 {
                        v_a_1579_ = crate::leanh::lean_ctor_get(v___x_1578_, 0);
                        v_isSharedCheck_1605_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1578_)) as u8;
                        if v_isSharedCheck_1605_ == 0 {
                            v___x_1581_ = v___x_1578_;
                            v_isShared_1582_ = v_isSharedCheck_1605_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1579_);
                            crate::leanh::lean_dec(v___x_1578_);
                            v___x_1581_ = crate::leanh::lean_box(0);
                            v_isShared_1582_ = v_isSharedCheck_1605_;
                            state = 33;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1388_, 6);
                        return v___x_1578_;
                    }
                }
                10 => {
                    v_fvarId_1606_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_cidx_1607_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    v_k_1608_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                    crate::leanh::lean_inc_ref(v_k_1608_);
                    v___x_1609_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1608_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                    if crate::leanh::lean_obj_tag(v___x_1609_) == 0 {
                        v_a_1610_ = crate::leanh::lean_ctor_get(v___x_1609_, 0);
                        v_isSharedCheck_1633_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1609_)) as u8;
                        if v_isSharedCheck_1633_ == 0 {
                            v___x_1612_ = v___x_1609_;
                            v_isShared_1613_ = v_isSharedCheck_1633_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1610_);
                            crate::leanh::lean_dec(v___x_1609_);
                            v___x_1612_ = crate::leanh::lean_box(0);
                            v_isShared_1613_ = v_isSharedCheck_1633_;
                            state = 38;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1388_, 3);
                        return v___x_1609_;
                    }
                }
                11 => {
                    v_fvarId_1634_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_n_1635_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    v_check_1636_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1388_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_1637_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1388_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_1638_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                    v_isSharedCheck_1691_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1691_ == 0 {
                        v___x_1640_ = v_code_1388_;
                        v_isShared_1641_ = v_isSharedCheck_1691_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_1638_);
                        crate::leanh::lean_inc(v_n_1635_);
                        crate::leanh::lean_inc(v_fvarId_1634_);
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1640_ = crate::leanh::lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1691_;
                        state = 43;
                        continue;
                    }
                }
                12 => {
                    v_fvarId_1692_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_n_1693_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    v_check_1694_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1388_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_1695_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_1388_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_1696_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                    v_k_1697_ = crate::leanh::lean_ctor_get(v_code_1388_, 3);
                    v_isSharedCheck_1750_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1750_ == 0 {
                        v___x_1699_ = v_code_1388_;
                        v_isShared_1700_ = v_isSharedCheck_1750_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_1697_);
                        crate::leanh::lean_inc(v_objs_x3f_1696_);
                        crate::leanh::lean_inc(v_n_1693_);
                        crate::leanh::lean_inc(v_fvarId_1692_);
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1699_ = crate::leanh::lean_box(0);
                        v_isShared_1700_ = v_isSharedCheck_1750_;
                        state = 52;
                        continue;
                    }
                }
                13 => {
                    v_fvarId_1751_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                    v_k_1752_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                    crate::leanh::lean_inc_ref(v_k_1752_);
                    v___x_1753_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1752_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                    if crate::leanh::lean_obj_tag(v___x_1753_) == 0 {
                        v_a_1754_ = crate::leanh::lean_ctor_get(v___x_1753_, 0);
                        v_isSharedCheck_1776_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1753_)) as u8;
                        if v_isSharedCheck_1776_ == 0 {
                            v___x_1756_ = v___x_1753_;
                            v_isShared_1757_ = v_isSharedCheck_1776_;
                            state = 61;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1754_);
                            crate::leanh::lean_dec(v___x_1753_);
                            v___x_1756_ = crate::leanh::lean_box(0);
                            v_isShared_1757_ = v_isSharedCheck_1776_;
                            state = 61;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1388_, 2);
                        return v___x_1753_;
                    }
                }
                _ => {
                    v___x_1777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1777_, 0, v_code_1388_);
                    return v___x_1777_;
                }
            },
            1 => {
                v___x_1402_ = lean_ptr_addr(v_k_1396_);
                v___x_1403_ = lean_ptr_addr(v_a_1398_);
                v___x_1404_ = lean_usize_dec_eq(v___x_1402_, v___x_1403_);
                if v___x_1404_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_1395_);
                    v_isSharedCheck_1414_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v_unused_1415_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                        crate::leanh::lean_dec(v_unused_1415_);
                        v_unused_1416_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1416_);
                        v___x_1406_ = v_code_1388_;
                        v_isShared_1407_ = v_isSharedCheck_1414_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1406_ = crate::leanh::lean_box(0);
                        v_isShared_1407_ = v_isSharedCheck_1414_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1398_);
                    if v_isShared_1401_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1400_, 0, v_code_1388_);
                        v___x_1418_ = v___x_1400_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_code_1388_);
                        v___x_1418_ = v_reuseFailAlloc_1419_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1406_, 1, v_a_1398_);
                    v___x_1409_ = v___x_1406_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_decl_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_a_1398_);
                    v___x_1409_ = v_reuseFailAlloc_1413_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1409_);
                    v___x_1411_ = v___x_1400_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1411_;
            }
            5 => {
                return v___x_1418_;
            }
            6 => {
                v___x_1453_ = lean_ptr_addr(v_k_1422_);
                v___x_1454_ = lean_ptr_addr(v_a_1432_);
                v___x_1455_ = lean_usize_dec_eq(v___x_1453_, v___x_1454_);
                if v___x_1455_ == 0 {
                    v___y_1437_ = v___x_1455_;
                    state = 7;
                    continue;
                } else {
                    v___x_1456_ = lean_ptr_addr(v_decl_1421_);
                    v___x_1457_ = lean_ptr_addr(v_a_1430_);
                    v___x_1458_ = lean_usize_dec_eq(v___x_1456_, v___x_1457_);
                    v___y_1437_ = v___x_1458_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_1437_ == 0 {
                    v_isSharedCheck_1447_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1447_ == 0 {
                        v_unused_1448_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                        crate::leanh::lean_dec(v_unused_1448_);
                        v_unused_1449_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1449_);
                        v___x_1439_ = v_code_1388_;
                        v_isShared_1440_ = v_isSharedCheck_1447_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1439_ = crate::leanh::lean_box(0);
                        v_isShared_1440_ = v_isSharedCheck_1447_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1432_);
                    crate::leanh::lean_dec(v_a_1430_);
                    if v_isShared_1435_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1434_, 0, v_code_1388_);
                        v___x_1451_ = v___x_1434_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_code_1388_);
                        v___x_1451_ = v_reuseFailAlloc_1452_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1439_, 1, v_a_1432_);
                    crate::leanh::lean_ctor_set(v___x_1439_, 0, v_a_1430_);
                    v___x_1442_ = v___x_1439_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1446_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_a_1432_);
                    v___x_1442_ = v_reuseFailAlloc_1446_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1435_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1442_);
                    v___x_1444_ = v___x_1434_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                    v___x_1444_ = v_reuseFailAlloc_1445_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1444_;
            }
            11 => {
                return v___x_1451_;
            }
            12 => {
                if v_isShared_1463_ == 0 {
                    v___x_1465_ = v___x_1462_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
                    v___x_1465_ = v_reuseFailAlloc_1466_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1465_;
            }
            14 => {
                v___x_1476_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_1472_);
                v___x_1477_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1(v___x_1476_, v_alts_1472_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                if crate::leanh::lean_obj_tag(v___x_1477_) == 0 {
                    v_a_1478_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                    v_isSharedCheck_1502_ = (!crate::leanh::lean_is_exclusive(v___x_1477_)) as u8;
                    if v_isSharedCheck_1502_ == 0 {
                        v___x_1480_ = v___x_1477_;
                        v_isShared_1481_ = v_isSharedCheck_1502_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1478_);
                        crate::leanh::lean_dec(v___x_1477_);
                        v___x_1480_ = crate::leanh::lean_box(0);
                        v_isShared_1481_ = v_isSharedCheck_1502_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1474_);
                    crate::leanh::lean_dec_ref(v_alts_1472_);
                    crate::leanh::lean_dec(v_discr_1471_);
                    crate::leanh::lean_dec_ref(v_resultType_1470_);
                    crate::leanh::lean_dec(v_typeName_1469_);
                    crate::leanh::lean_dec_ref_known(v_code_1388_, 1);
                    v_a_1503_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                    v_isSharedCheck_1510_ = (!crate::leanh::lean_is_exclusive(v___x_1477_)) as u8;
                    if v_isSharedCheck_1510_ == 0 {
                        v___x_1505_ = v___x_1477_;
                        v_isShared_1506_ = v_isSharedCheck_1510_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1503_);
                        crate::leanh::lean_dec(v___x_1477_);
                        v___x_1505_ = crate::leanh::lean_box(0);
                        v_isShared_1506_ = v_isSharedCheck_1510_;
                        state = 21;
                        continue;
                    }
                }
            }
            15 => {
                v___x_1482_ = lean_ptr_addr(v_alts_1472_);
                crate::leanh::lean_dec_ref(v_alts_1472_);
                v___x_1483_ = lean_ptr_addr(v_a_1478_);
                v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
                if v___x_1484_ == 0 {
                    v_isSharedCheck_1497_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v_unused_1498_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1498_);
                        v___x_1486_ = v_code_1388_;
                        v_isShared_1487_ = v_isSharedCheck_1497_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1486_ = crate::leanh::lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1497_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1478_);
                    crate::leanh::lean_del_object(v___x_1474_);
                    crate::leanh::lean_dec(v_discr_1471_);
                    crate::leanh::lean_dec_ref(v_resultType_1470_);
                    crate::leanh::lean_dec(v_typeName_1469_);
                    if v_isShared_1481_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1480_, 0, v_code_1388_);
                        v___x_1500_ = v___x_1480_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_code_1388_);
                        v___x_1500_ = v_reuseFailAlloc_1501_;
                        state = 20;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_1475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1474_, 3, v_a_1478_);
                    v___x_1489_ = v___x_1474_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_typeName_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_resultType_1470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_discr_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 3, v_a_1478_);
                    v___x_1489_ = v_reuseFailAlloc_1496_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1486_, 0, v___x_1489_);
                    v___x_1491_ = v___x_1486_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1495_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1489_);
                    v___x_1491_ = v_reuseFailAlloc_1495_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1480_, 0, v___x_1491_);
                    v___x_1493_ = v___x_1480_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
                    v___x_1493_ = v_reuseFailAlloc_1494_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1493_;
            }
            20 => {
                return v___x_1500_;
            }
            21 => {
                if v_isShared_1506_ == 0 {
                    v___x_1508_ = v___x_1505_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
                    v___x_1508_ = v_reuseFailAlloc_1509_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1508_;
            }
            23 => {
                v___x_1521_ = lean_ptr_addr(v_k_1515_);
                v___x_1522_ = lean_ptr_addr(v_a_1517_);
                v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
                if v___x_1523_ == 0 {
                    crate::leanh::lean_inc(v_y_1514_);
                    crate::leanh::lean_inc(v_i_1513_);
                    crate::leanh::lean_inc(v_fvarId_1512_);
                    v_isSharedCheck_1533_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1533_ == 0 {
                        v_unused_1534_ = crate::leanh::lean_ctor_get(v_code_1388_, 3);
                        crate::leanh::lean_dec(v_unused_1534_);
                        v_unused_1535_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                        crate::leanh::lean_dec(v_unused_1535_);
                        v_unused_1536_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                        crate::leanh::lean_dec(v_unused_1536_);
                        v_unused_1537_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1537_);
                        v___x_1525_ = v_code_1388_;
                        v_isShared_1526_ = v_isSharedCheck_1533_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1525_ = crate::leanh::lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1533_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1517_);
                    if v_isShared_1520_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1519_, 0, v_code_1388_);
                        v___x_1539_ = v___x_1519_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_code_1388_);
                        v___x_1539_ = v_reuseFailAlloc_1540_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_1526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1525_, 3, v_a_1517_);
                    v___x_1528_ = v___x_1525_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_fvarId_1512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_i_1513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_y_1514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_a_1517_);
                    v___x_1528_ = v_reuseFailAlloc_1532_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_1520_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1519_, 0, v___x_1528_);
                    v___x_1530_ = v___x_1519_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
                    v___x_1530_ = v_reuseFailAlloc_1531_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1530_;
            }
            27 => {
                return v___x_1539_;
            }
            28 => {
                v___x_1551_ = lean_ptr_addr(v_k_1545_);
                v___x_1552_ = lean_ptr_addr(v_a_1547_);
                v___x_1553_ = lean_usize_dec_eq(v___x_1551_, v___x_1552_);
                if v___x_1553_ == 0 {
                    crate::leanh::lean_inc(v_y_1544_);
                    crate::leanh::lean_inc(v_i_1543_);
                    crate::leanh::lean_inc(v_fvarId_1542_);
                    v_isSharedCheck_1563_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1563_ == 0 {
                        v_unused_1564_ = crate::leanh::lean_ctor_get(v_code_1388_, 3);
                        crate::leanh::lean_dec(v_unused_1564_);
                        v_unused_1565_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                        crate::leanh::lean_dec(v_unused_1565_);
                        v_unused_1566_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                        crate::leanh::lean_dec(v_unused_1566_);
                        v_unused_1567_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1567_);
                        v___x_1555_ = v_code_1388_;
                        v_isShared_1556_ = v_isSharedCheck_1563_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1555_ = crate::leanh::lean_box(0);
                        v_isShared_1556_ = v_isSharedCheck_1563_;
                        state = 29;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1547_);
                    if v_isShared_1550_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1549_, 0, v_code_1388_);
                        v___x_1569_ = v___x_1549_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_1570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_code_1388_);
                        v___x_1569_ = v_reuseFailAlloc_1570_;
                        state = 32;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_1556_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1555_, 3, v_a_1547_);
                    v___x_1558_ = v___x_1555_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_fvarId_1542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_i_1543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_y_1544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_a_1547_);
                    v___x_1558_ = v_reuseFailAlloc_1562_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_1550_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1549_, 0, v___x_1558_);
                    v___x_1560_ = v___x_1549_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
                    v___x_1560_ = v_reuseFailAlloc_1561_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1560_;
            }
            32 => {
                return v___x_1569_;
            }
            33 => {
                v___x_1583_ = lean_ptr_addr(v_k_1577_);
                v___x_1584_ = lean_ptr_addr(v_a_1579_);
                v___x_1585_ = lean_usize_dec_eq(v___x_1583_, v___x_1584_);
                if v___x_1585_ == 0 {
                    crate::leanh::lean_inc_ref(v_ty_1576_);
                    crate::leanh::lean_inc(v_y_1575_);
                    crate::leanh::lean_inc(v_offset_1574_);
                    crate::leanh::lean_inc(v_i_1573_);
                    crate::leanh::lean_inc(v_fvarId_1572_);
                    v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1595_ == 0 {
                        v_unused_1596_ = crate::leanh::lean_ctor_get(v_code_1388_, 5);
                        crate::leanh::lean_dec(v_unused_1596_);
                        v_unused_1597_ = crate::leanh::lean_ctor_get(v_code_1388_, 4);
                        crate::leanh::lean_dec(v_unused_1597_);
                        v_unused_1598_ = crate::leanh::lean_ctor_get(v_code_1388_, 3);
                        crate::leanh::lean_dec(v_unused_1598_);
                        v_unused_1599_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                        crate::leanh::lean_dec(v_unused_1599_);
                        v_unused_1600_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                        crate::leanh::lean_dec(v_unused_1600_);
                        v_unused_1601_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1601_);
                        v___x_1587_ = v_code_1388_;
                        v_isShared_1588_ = v_isSharedCheck_1595_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1587_ = crate::leanh::lean_box(0);
                        v_isShared_1588_ = v_isSharedCheck_1595_;
                        state = 34;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1579_);
                    if v_isShared_1582_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1581_, 0, v_code_1388_);
                        v___x_1603_ = v___x_1581_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_1604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_code_1388_);
                        v___x_1603_ = v_reuseFailAlloc_1604_;
                        state = 37;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_1588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1587_, 5, v_a_1579_);
                    v___x_1590_ = v___x_1587_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_fvarId_1572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_i_1573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_offset_1574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_y_1575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_ty_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 5, v_a_1579_);
                    v___x_1590_ = v_reuseFailAlloc_1594_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1590_);
                    v___x_1592_ = v___x_1581_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1592_;
            }
            37 => {
                return v___x_1603_;
            }
            38 => {
                v___x_1614_ = lean_ptr_addr(v_k_1608_);
                v___x_1615_ = lean_ptr_addr(v_a_1610_);
                v___x_1616_ = lean_usize_dec_eq(v___x_1614_, v___x_1615_);
                if v___x_1616_ == 0 {
                    crate::leanh::lean_inc(v_cidx_1607_);
                    crate::leanh::lean_inc(v_fvarId_1606_);
                    v_isSharedCheck_1626_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1626_ == 0 {
                        v_unused_1627_ = crate::leanh::lean_ctor_get(v_code_1388_, 2);
                        crate::leanh::lean_dec(v_unused_1627_);
                        v_unused_1628_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                        crate::leanh::lean_dec(v_unused_1628_);
                        v_unused_1629_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1629_);
                        v___x_1618_ = v_code_1388_;
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1618_ = crate::leanh::lean_box(0);
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 39;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1610_);
                    if v_isShared_1613_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1612_, 0, v_code_1388_);
                        v___x_1631_ = v___x_1612_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_1632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_code_1388_);
                        v___x_1631_ = v_reuseFailAlloc_1632_;
                        state = 42;
                        continue;
                    }
                }
            }
            39 => {
                if v_isShared_1619_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1618_, 2, v_a_1610_);
                    v___x_1621_ = v___x_1618_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_fvarId_1606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_cidx_1607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_a_1610_);
                    v___x_1621_ = v_reuseFailAlloc_1625_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1613_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1612_, 0, v___x_1621_);
                    v___x_1623_ = v___x_1612_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
                    v___x_1623_ = v_reuseFailAlloc_1624_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1623_;
            }
            42 => {
                return v___x_1631_;
            }
            43 => {
                v___x_1642_ = lean_st_ref_take(v_a_1389_);
                v_incTotal_1643_ = crate::leanh::lean_ctor_get(v___x_1642_, 0);
                v_decTotal_1644_ = crate::leanh::lean_ctor_get(v___x_1642_, 1);
                v_incAccum_1645_ = crate::leanh::lean_ctor_get(v___x_1642_, 2);
                v_decPlaced_1646_ = crate::leanh::lean_ctor_get(v___x_1642_, 3);
                v_isSharedCheck_1690_ = (!crate::leanh::lean_is_exclusive(v___x_1642_)) as u8;
                if v_isSharedCheck_1690_ == 0 {
                    v___x_1648_ = v___x_1642_;
                    v_isShared_1649_ = v_isSharedCheck_1690_;
                    state = 44;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decPlaced_1646_);
                    crate::leanh::lean_inc(v_incAccum_1645_);
                    crate::leanh::lean_inc(v_decTotal_1644_);
                    crate::leanh::lean_inc(v_incTotal_1643_);
                    crate::leanh::lean_dec(v___x_1642_);
                    v___x_1648_ = crate::leanh::lean_box(0);
                    v_isShared_1649_ = v_isSharedCheck_1690_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                crate::leanh::lean_inc(v_fvarId_1634_);
                crate::leanh::lean_inc(v_n_1635_);
                v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(v_n_1635_, v_incTotal_1643_, v_fvarId_1634_);
                if v_isShared_1649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1648_, 0, v___x_1650_);
                    v___x_1652_ = v___x_1648_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1689_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_decTotal_1644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_incAccum_1645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_decPlaced_1646_);
                    v___x_1652_ = v_reuseFailAlloc_1689_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                v___x_1653_ = lean_st_ref_set(v_a_1389_, v___x_1652_);
                v___x_1654_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1638_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                if crate::leanh::lean_obj_tag(v___x_1654_) == 0 {
                    v_a_1655_ = crate::leanh::lean_ctor_get(v___x_1654_, 0);
                    v_isSharedCheck_1688_ = (!crate::leanh::lean_is_exclusive(v___x_1654_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v___x_1657_ = v___x_1654_;
                        v_isShared_1658_ = v_isSharedCheck_1688_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1655_);
                        crate::leanh::lean_dec(v___x_1654_);
                        v___x_1657_ = crate::leanh::lean_box(0);
                        v_isShared_1658_ = v_isSharedCheck_1688_;
                        state = 46;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1640_);
                    crate::leanh::lean_dec(v_n_1635_);
                    crate::leanh::lean_dec(v_fvarId_1634_);
                    return v___x_1654_;
                }
            }
            46 => {
                v___x_1659_ = lean_st_ref_take(v_a_1389_);
                v_incTotal_1660_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
                v_decTotal_1661_ = crate::leanh::lean_ctor_get(v___x_1659_, 1);
                v_incAccum_1662_ = crate::leanh::lean_ctor_get(v___x_1659_, 2);
                v_decPlaced_1663_ = crate::leanh::lean_ctor_get(v___x_1659_, 3);
                v_isSharedCheck_1687_ = (!crate::leanh::lean_is_exclusive(v___x_1659_)) as u8;
                if v_isSharedCheck_1687_ == 0 {
                    v___x_1665_ = v___x_1659_;
                    v_isShared_1666_ = v_isSharedCheck_1687_;
                    state = 47;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decPlaced_1663_);
                    crate::leanh::lean_inc(v_incAccum_1662_);
                    crate::leanh::lean_inc(v_decTotal_1661_);
                    crate::leanh::lean_inc(v_incTotal_1660_);
                    crate::leanh::lean_dec(v___x_1659_);
                    v___x_1665_ = crate::leanh::lean_box(0);
                    v_isShared_1666_ = v_isSharedCheck_1687_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                crate::leanh::lean_inc(v_fvarId_1634_);
                v___x_1667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(v_n_1635_, v_incAccum_1662_, v_fvarId_1634_);
                if v_isShared_1666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1665_, 2, v___x_1667_);
                    v___x_1669_ = v___x_1665_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_incTotal_1660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_decTotal_1661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 2, v___x_1667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_decPlaced_1663_);
                    v___x_1669_ = v_reuseFailAlloc_1686_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                v___x_1670_ = lean_st_ref_set(v_a_1389_, v___x_1669_);
                v___x_1671_ = lean_st_ref_get(v_a_1389_);
                v_incTotal_1672_ = crate::leanh::lean_ctor_get(v___x_1671_, 0);
                crate::leanh::lean_inc_ref(v_incTotal_1672_);
                v_incAccum_1673_ = crate::leanh::lean_ctor_get(v___x_1671_, 2);
                crate::leanh::lean_inc_ref(v_incAccum_1673_);
                crate::leanh::lean_dec(v___x_1671_);
                v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(v_incAccum_1673_, v_fvarId_1634_);
                crate::leanh::lean_dec_ref(v_incAccum_1673_);
                v___x_1675_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(v_incTotal_1672_, v_fvarId_1634_);
                crate::leanh::lean_dec_ref(v_incTotal_1672_);
                v___x_1676_ = lean_nat_dec_eq(v___x_1674_, v___x_1675_);
                crate::leanh::lean_dec(v___x_1674_);
                if v___x_1676_ == 0 {
                    crate::leanh::lean_dec(v___x_1675_);
                    crate::leanh::lean_del_object(v___x_1640_);
                    crate::leanh::lean_dec(v_fvarId_1634_);
                    if v_isShared_1658_ == 0 {
                        v___x_1678_ = v___x_1657_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_1679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1655_);
                        v___x_1678_ = v_reuseFailAlloc_1679_;
                        state = 49;
                        continue;
                    }
                } else {
                    if v_isShared_1641_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1640_, 2, v_a_1655_);
                        crate::leanh::lean_ctor_set(v___x_1640_, 1, v___x_1675_);
                        v___x_1681_ = v___x_1640_;
                        state = 50;
                        continue;
                    } else {
                        v_reuseFailAlloc_1685_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_fvarId_1634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 1, v___x_1675_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_a_1655_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1685_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v_check_1636_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1685_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                            v_persistent_1637_,
                        );
                        v___x_1681_ = v_reuseFailAlloc_1685_;
                        state = 50;
                        continue;
                    }
                }
            }
            49 => {
                return v___x_1678_;
            }
            50 => {
                if v_isShared_1658_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1657_, 0, v___x_1681_);
                    v___x_1683_ = v___x_1657_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_1684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
                    v___x_1683_ = v_reuseFailAlloc_1684_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_1683_;
            }
            52 => {
                v___x_1701_ = lean_st_ref_take(v_a_1389_);
                v_incTotal_1702_ = crate::leanh::lean_ctor_get(v___x_1701_, 0);
                v_decTotal_1703_ = crate::leanh::lean_ctor_get(v___x_1701_, 1);
                v_incAccum_1704_ = crate::leanh::lean_ctor_get(v___x_1701_, 2);
                v_decPlaced_1705_ = crate::leanh::lean_ctor_get(v___x_1701_, 3);
                v_isSharedCheck_1749_ = (!crate::leanh::lean_is_exclusive(v___x_1701_)) as u8;
                if v_isSharedCheck_1749_ == 0 {
                    v___x_1707_ = v___x_1701_;
                    v_isShared_1708_ = v_isSharedCheck_1749_;
                    state = 53;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decPlaced_1705_);
                    crate::leanh::lean_inc(v_incAccum_1704_);
                    crate::leanh::lean_inc(v_decTotal_1703_);
                    crate::leanh::lean_inc(v_incTotal_1702_);
                    crate::leanh::lean_dec(v___x_1701_);
                    v___x_1707_ = crate::leanh::lean_box(0);
                    v_isShared_1708_ = v_isSharedCheck_1749_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                crate::leanh::lean_inc(v_fvarId_1692_);
                v___x_1709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2(v_n_1693_, v_decTotal_1703_, v_fvarId_1692_);
                if v_isShared_1708_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1707_, 1, v___x_1709_);
                    v___x_1711_ = v___x_1707_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_1748_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_incTotal_1702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_incAccum_1704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_decPlaced_1705_);
                    v___x_1711_ = v_reuseFailAlloc_1748_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v___x_1712_ = lean_st_ref_set(v_a_1389_, v___x_1711_);
                v___x_1713_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_k_1697_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
                if crate::leanh::lean_obj_tag(v___x_1713_) == 0 {
                    v_a_1714_ = crate::leanh::lean_ctor_get(v___x_1713_, 0);
                    v_isSharedCheck_1747_ = (!crate::leanh::lean_is_exclusive(v___x_1713_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1716_ = v___x_1713_;
                        v_isShared_1717_ = v_isSharedCheck_1747_;
                        state = 55;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1714_);
                        crate::leanh::lean_dec(v___x_1713_);
                        v___x_1716_ = crate::leanh::lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1747_;
                        state = 55;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1699_);
                    crate::leanh::lean_dec(v_objs_x3f_1696_);
                    crate::leanh::lean_dec(v_fvarId_1692_);
                    return v___x_1713_;
                }
            }
            55 => {
                v___x_1718_ = lean_st_ref_get(v_a_1389_);
                v_decTotal_1719_ = crate::leanh::lean_ctor_get(v___x_1718_, 1);
                crate::leanh::lean_inc_ref(v_decTotal_1719_);
                v_decPlaced_1720_ = crate::leanh::lean_ctor_get(v___x_1718_, 3);
                crate::leanh::lean_inc_ref(v_decPlaced_1720_);
                crate::leanh::lean_dec(v___x_1718_);
                v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_decPlaced_1720_, v_fvarId_1692_);
                crate::leanh::lean_dec_ref(v_decPlaced_1720_);
                if v___x_1721_ == 0 {
                    v___x_1722_ = lean_st_ref_take(v_a_1389_);
                    v_incTotal_1723_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
                    v_decTotal_1724_ = crate::leanh::lean_ctor_get(v___x_1722_, 1);
                    v_incAccum_1725_ = crate::leanh::lean_ctor_get(v___x_1722_, 2);
                    v_decPlaced_1726_ = crate::leanh::lean_ctor_get(v___x_1722_, 3);
                    v_isSharedCheck_1743_ = (!crate::leanh::lean_is_exclusive(v___x_1722_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v___x_1728_ = v___x_1722_;
                        v_isShared_1729_ = v_isSharedCheck_1743_;
                        state = 56;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_decPlaced_1726_);
                        crate::leanh::lean_inc(v_incAccum_1725_);
                        crate::leanh::lean_inc(v_decTotal_1724_);
                        crate::leanh::lean_inc(v_incTotal_1723_);
                        crate::leanh::lean_dec(v___x_1722_);
                        v___x_1728_ = crate::leanh::lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1743_;
                        state = 56;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decTotal_1719_);
                    crate::leanh::lean_del_object(v___x_1699_);
                    crate::leanh::lean_dec(v_objs_x3f_1696_);
                    crate::leanh::lean_dec(v_fvarId_1692_);
                    if v_isShared_1717_ == 0 {
                        v___x_1745_ = v___x_1716_;
                        state = 60;
                        continue;
                    } else {
                        v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1714_);
                        v___x_1745_ = v_reuseFailAlloc_1746_;
                        state = 60;
                        continue;
                    }
                }
            }
            56 => {
                v___x_1730_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fvarId_1692_);
                v___x_1731_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(v_decPlaced_1726_, v_fvarId_1692_, v___x_1730_);
                if v_isShared_1729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1728_, 3, v___x_1731_);
                    v___x_1733_ = v___x_1728_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_incTotal_1723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_decTotal_1724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_incAccum_1725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 3, v___x_1731_);
                    v___x_1733_ = v_reuseFailAlloc_1742_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                v___x_1734_ = lean_st_ref_set(v_a_1389_, v___x_1733_);
                v___x_1735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__3(v_decTotal_1719_, v_fvarId_1692_);
                crate::leanh::lean_dec_ref(v_decTotal_1719_);
                if v_isShared_1700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1699_, 3, v_a_1714_);
                    crate::leanh::lean_ctor_set(v___x_1699_, 1, v___x_1735_);
                    v___x_1737_ = v___x_1699_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_fvarId_1692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_objs_x3f_1696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_a_1714_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1741_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_1694_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1741_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_1695_,
                    );
                    v___x_1737_ = v_reuseFailAlloc_1741_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                if v_isShared_1717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1716_, 0, v___x_1737_);
                    v___x_1739_ = v___x_1716_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
                    v___x_1739_ = v_reuseFailAlloc_1740_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_1739_;
            }
            60 => {
                return v___x_1745_;
            }
            61 => {
                v___x_1758_ = lean_ptr_addr(v_k_1752_);
                v___x_1759_ = lean_ptr_addr(v_a_1754_);
                v___x_1760_ = lean_usize_dec_eq(v___x_1758_, v___x_1759_);
                if v___x_1760_ == 0 {
                    crate::leanh::lean_inc(v_fvarId_1751_);
                    v_isSharedCheck_1770_ = (!crate::leanh::lean_is_exclusive(v_code_1388_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v_unused_1771_ = crate::leanh::lean_ctor_get(v_code_1388_, 1);
                        crate::leanh::lean_dec(v_unused_1771_);
                        v_unused_1772_ = crate::leanh::lean_ctor_get(v_code_1388_, 0);
                        crate::leanh::lean_dec(v_unused_1772_);
                        v___x_1762_ = v_code_1388_;
                        v_isShared_1763_ = v_isSharedCheck_1770_;
                        state = 62;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1388_);
                        v___x_1762_ = crate::leanh::lean_box(0);
                        v_isShared_1763_ = v_isSharedCheck_1770_;
                        state = 62;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1754_);
                    if v_isShared_1757_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1756_, 0, v_code_1388_);
                        v___x_1774_ = v___x_1756_;
                        state = 65;
                        continue;
                    } else {
                        v_reuseFailAlloc_1775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_code_1388_);
                        v___x_1774_ = v_reuseFailAlloc_1775_;
                        state = 65;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_1763_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1762_, 1, v_a_1754_);
                    v___x_1765_ = v___x_1762_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_1769_ = crate::leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_fvarId_1751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_a_1754_);
                    v___x_1765_ = v_reuseFailAlloc_1769_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_1757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1765_);
                    v___x_1767_ = v___x_1756_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
                    v___x_1767_ = v_reuseFailAlloc_1768_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_1767_;
            }
            65 => {
                return v___x_1774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(
    mut v_code_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
    mut v_a_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1784_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2_once), _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___closed__2);
                v___x_1785_ = lean_st_mk_ref(v___x_1784_);
                v___x_1786_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(v_code_1778_, v___x_1785_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
                if crate::leanh::lean_obj_tag(v___x_1786_) == 0 {
                    v_a_1787_ = crate::leanh::lean_ctor_get(v___x_1786_, 0);
                    v_isSharedCheck_1795_ = (!crate::leanh::lean_is_exclusive(v___x_1786_)) as u8;
                    if v_isSharedCheck_1795_ == 0 {
                        v___x_1789_ = v___x_1786_;
                        v_isShared_1790_ = v_isSharedCheck_1795_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1787_);
                        crate::leanh::lean_dec(v___x_1786_);
                        v___x_1789_ = crate::leanh::lean_box(0);
                        v_isShared_1790_ = v_isSharedCheck_1795_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1785_);
                    return v___x_1786_;
                }
            }
            1 => {
                v___x_1791_ = lean_st_ref_get(v___x_1785_);
                crate::leanh::lean_dec(v___x_1785_);
                crate::leanh::lean_dec(v___x_1791_);
                if v_isShared_1790_ == 0 {
                    v___x_1793_ = v___x_1789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1787_);
                    v___x_1793_ = v_reuseFailAlloc_1794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___lam__0(
    mut v_x_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(
        v_x_1796_,
        v___y_1798_,
        v___y_1799_,
        v___y_1800_,
        v___y_1801_,
    );
    return v___x_1803_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC___boxed(
    mut v_code_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
    mut v_a_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC(
        v_code_1804_,
        v_a_1805_,
        v_a_1806_,
        v_a_1807_,
        v_a_1808_,
    );
    crate::leanh::lean_dec(v_a_1808_);
    crate::leanh::lean_dec_ref(v_a_1807_);
    crate::leanh::lean_dec(v_a_1806_);
    crate::leanh::lean_dec_ref(v_a_1805_);
    return v_res_1810_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1___boxed(
    mut v_i_1811_: *mut crate::leanh::LeanObject,
    mut v_as_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1819_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__1(v_i_1811_, v_as_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
    crate::leanh::lean_dec(v___y_1817_);
    crate::leanh::lean_dec_ref(v___y_1816_);
    crate::leanh::lean_dec(v___y_1815_);
    crate::leanh::lean_dec_ref(v___y_1814_);
    crate::leanh::lean_dec(v___y_1813_);
    return v_res_1819_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go___boxed(
    mut v_code_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
    mut v_a_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1827_ =
        l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go(
            v_code_1820_,
            v_a_1821_,
            v_a_1822_,
            v_a_1823_,
            v_a_1824_,
            v_a_1825_,
        );
    crate::leanh::lean_dec(v_a_1825_);
    crate::leanh::lean_dec_ref(v_a_1824_);
    crate::leanh::lean_dec(v_a_1823_);
    crate::leanh::lean_dec_ref(v_a_1822_);
    crate::leanh::lean_dec(v_a_1821_);
    return v_res_1827_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0(
    mut v_pu_1828_: u8,
    mut v_alt_1829_: *mut crate::leanh::LeanObject,
    mut v_f_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
    mut v___y_1834_: *mut crate::leanh::LeanObject,
    mut v___y_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1837_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___redArg(v_alt_1829_, v_f_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
    return v___x_1837_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0___boxed(
    mut v_pu_1838_: *mut crate::leanh::LeanObject,
    mut v_alt_1839_: *mut crate::leanh::LeanObject,
    mut v_f_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1847_: u8 = 0;
    let mut v_res_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1847_ = (crate::leanh::lean_unbox(v_pu_1838_) as u8);
    v_res_1848_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__0(v_pu_boxed_1847_, v_alt_1839_, v_f_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
    crate::leanh::lean_dec(v___y_1845_);
    crate::leanh::lean_dec_ref(v___y_1844_);
    crate::leanh::lean_dec(v___y_1843_);
    crate::leanh::lean_dec_ref(v___y_1842_);
    crate::leanh::lean_dec(v___y_1841_);
    return v_res_1848_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4(
    mut v_00_u03b2_1849_: *mut crate::leanh::LeanObject,
    mut v_m_1850_: *mut crate::leanh::LeanObject,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1852_: u8 = 0;
    v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___redArg(v_m_1850_, v_a_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4___boxed(
    mut v_00_u03b2_1853_: *mut crate::leanh::LeanObject,
    mut v_m_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1856_: u8 = 0;
    let mut v_r_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__4(v_00_u03b2_1853_, v_m_1854_, v_a_1855_);
    crate::leanh::lean_dec(v_a_1855_);
    crate::leanh::lean_dec_ref(v_m_1854_);
    v_r_1857_ = crate::leanh::lean_box((v_res_1856_) as usize);
    return v_r_1857_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5(
    mut v_00_u03b2_1858_: *mut crate::leanh::LeanObject,
    mut v_m_1859_: *mut crate::leanh::LeanObject,
    mut v_a_1860_: *mut crate::leanh::LeanObject,
    mut v_b_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__5___redArg(v_m_1859_, v_a_1860_, v_b_1861_);
    return v___x_1862_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3(
    mut v_00_u03b2_1863_: *mut crate::leanh::LeanObject,
    mut v_a_1864_: *mut crate::leanh::LeanObject,
    mut v_x_1865_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1866_: u8 = 0;
    v___x_1866_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___redArg(v_a_1864_, v_x_1865_);
    return v___x_1866_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3___boxed(
    mut v_00_u03b2_1867_: *mut crate::leanh::LeanObject,
    mut v_a_1868_: *mut crate::leanh::LeanObject,
    mut v_x_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1870_: u8 = 0;
    let mut v_r_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__3(v_00_u03b2_1867_, v_a_1868_, v_x_1869_);
    crate::leanh::lean_dec(v_x_1869_);
    crate::leanh::lean_dec(v_a_1868_);
    v_r_1871_ = crate::leanh::lean_box((v_res_1870_) as usize);
    return v_r_1871_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4(
    mut v_00_u03b2_1872_: *mut crate::leanh::LeanObject,
    mut v_data_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4___redArg(v_data_1873_);
    return v___x_1874_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1875_: *mut crate::leanh::LeanObject,
    mut v_i_1876_: *mut crate::leanh::LeanObject,
    mut v_source_1877_: *mut crate::leanh::LeanObject,
    mut v_target_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5___redArg(v_i_1876_, v_source_1877_, v_target_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5_spec__9(
    mut v_00_u03b2_1880_: *mut crate::leanh::LeanObject,
    mut v_x_1881_: *mut crate::leanh::LeanObject,
    mut v_x_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Code_coalesceRC_go_spec__2_spec__4_spec__5_spec__9___redArg(v_x_1881_, v_x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(
    mut v_f_1884_: *mut crate::leanh::LeanObject,
    mut v_v_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1906_: u8 = 0;
    let mut v_a_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1910_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1914_: u8 = 0;
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_1885_) == 0 {
                    v_code_1891_ = crate::leanh::lean_ctor_get(v_v_1885_, 0);
                    v_isSharedCheck_1915_ = (!crate::leanh::lean_is_exclusive(v_v_1885_)) as u8;
                    if v_isSharedCheck_1915_ == 0 {
                        v___x_1893_ = v_v_1885_;
                        v_isShared_1894_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_1891_);
                        crate::leanh::lean_dec(v_v_1885_);
                        v___x_1893_ = crate::leanh::lean_box(0);
                        v_isShared_1894_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_1884_);
                    v___x_1916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1916_, 0, v_v_1885_);
                    return v___x_1916_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1889_);
                crate::leanh::lean_inc_ref(v___y_1888_);
                crate::leanh::lean_inc(v___y_1887_);
                crate::leanh::lean_inc_ref(v___y_1886_);
                v___x_1895_ = crate::leanh::lean_apply_6(
                    v_f_1884_,
                    v_code_1891_,
                    v___y_1886_,
                    v___y_1887_,
                    v___y_1888_,
                    v___y_1889_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1895_) == 0 {
                    v_a_1896_ = crate::leanh::lean_ctor_get(v___x_1895_, 0);
                    v_isSharedCheck_1906_ = (!crate::leanh::lean_is_exclusive(v___x_1895_)) as u8;
                    if v_isSharedCheck_1906_ == 0 {
                        v___x_1898_ = v___x_1895_;
                        v_isShared_1899_ = v_isSharedCheck_1906_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1896_);
                        crate::leanh::lean_dec(v___x_1895_);
                        v___x_1898_ = crate::leanh::lean_box(0);
                        v_isShared_1899_ = v_isSharedCheck_1906_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1893_);
                    v_a_1907_ = crate::leanh::lean_ctor_get(v___x_1895_, 0);
                    v_isSharedCheck_1914_ = (!crate::leanh::lean_is_exclusive(v___x_1895_)) as u8;
                    if v_isSharedCheck_1914_ == 0 {
                        v___x_1909_ = v___x_1895_;
                        v_isShared_1910_ = v_isSharedCheck_1914_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1907_);
                        crate::leanh::lean_dec(v___x_1895_);
                        v___x_1909_ = crate::leanh::lean_box(0);
                        v_isShared_1910_ = v_isSharedCheck_1914_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1894_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1893_, 0, v_a_1896_);
                    v___x_1901_ = v___x_1893_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1896_);
                    v___x_1901_ = v_reuseFailAlloc_1905_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1901_);
                    v___x_1903_ = v___x_1898_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
                    v___x_1903_ = v_reuseFailAlloc_1904_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1903_;
            }
            5 => {
                if v_isShared_1910_ == 0 {
                    v___x_1912_ = v___x_1909_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
                    v___x_1912_ = v_reuseFailAlloc_1913_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg___boxed(
    mut v_f_1917_: *mut crate::leanh::LeanObject,
    mut v_v_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(v_f_1917_, v_v_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
    crate::leanh::lean_dec(v___y_1922_);
    crate::leanh::lean_dec_ref(v___y_1921_);
    crate::leanh::lean_dec(v___y_1920_);
    crate::leanh::lean_dec_ref(v___y_1919_);
    return v_res_1924_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0(
    mut v_pu_1925_: u8,
    mut v_f_1926_: *mut crate::leanh::LeanObject,
    mut v_v_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(v_f_1926_, v_v_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
    return v___x_1933_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___boxed(
    mut v_pu_1934_: *mut crate::leanh::LeanObject,
    mut v_f_1935_: *mut crate::leanh::LeanObject,
    mut v_v_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1942_: u8 = 0;
    let mut v_res_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1942_ = (crate::leanh::lean_unbox(v_pu_1934_) as u8);
    v_res_1943_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0(v_pu_boxed_1942_, v_f_1935_, v_v_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
    crate::leanh::lean_dec(v___y_1940_);
    crate::leanh::lean_dec_ref(v___y_1939_);
    crate::leanh::lean_dec(v___y_1938_);
    crate::leanh::lean_dec_ref(v___y_1937_);
    return v_res_1943_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC(
    mut v_decl_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_1953_: u8 = 0;
    let mut v_inlineAttr_x3f_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1957_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1970_: u8 = 0;
    let mut v_a_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_1951_ = crate::leanh::lean_ctor_get(v_decl_1945_, 0);
                v_value_1952_ = crate::leanh::lean_ctor_get(v_decl_1945_, 1);
                v_recursive_1953_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_1945_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_1954_ = crate::leanh::lean_ctor_get(v_decl_1945_, 2);
                v_isSharedCheck_1979_ = (!crate::leanh::lean_is_exclusive(v_decl_1945_)) as u8;
                if v_isSharedCheck_1979_ == 0 {
                    v___x_1956_ = v_decl_1945_;
                    v_isShared_1957_ = v_isSharedCheck_1979_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_1954_);
                    crate::leanh::lean_inc(v_value_1952_);
                    crate::leanh::lean_inc(v_toSignature_1951_);
                    crate::leanh::lean_dec(v_decl_1945_);
                    v___x_1956_ = crate::leanh::lean_box(0);
                    v_isShared_1957_ = v_isSharedCheck_1979_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1958_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___closed__0;
                v___x_1959_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC_spec__0___redArg(v___x_1958_, v_value_1952_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
                if crate::leanh::lean_obj_tag(v___x_1959_) == 0 {
                    v_a_1960_ = crate::leanh::lean_ctor_get(v___x_1959_, 0);
                    v_isSharedCheck_1970_ = (!crate::leanh::lean_is_exclusive(v___x_1959_)) as u8;
                    if v_isSharedCheck_1970_ == 0 {
                        v___x_1962_ = v___x_1959_;
                        v_isShared_1963_ = v_isSharedCheck_1970_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1960_);
                        crate::leanh::lean_dec(v___x_1959_);
                        v___x_1962_ = crate::leanh::lean_box(0);
                        v_isShared_1963_ = v_isSharedCheck_1970_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1956_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_1954_);
                    crate::leanh::lean_dec_ref(v_toSignature_1951_);
                    v_a_1971_ = crate::leanh::lean_ctor_get(v___x_1959_, 0);
                    v_isSharedCheck_1978_ = (!crate::leanh::lean_is_exclusive(v___x_1959_)) as u8;
                    if v_isSharedCheck_1978_ == 0 {
                        v___x_1973_ = v___x_1959_;
                        v_isShared_1974_ = v_isSharedCheck_1978_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1971_);
                        crate::leanh::lean_dec(v___x_1959_);
                        v___x_1973_ = crate::leanh::lean_box(0);
                        v_isShared_1974_ = v_isSharedCheck_1978_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1956_, 1, v_a_1960_);
                    v___x_1965_ = v___x_1956_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1969_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_toSignature_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_a_1960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_inlineAttr_x3f_1954_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1969_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_1953_,
                    );
                    v___x_1965_ = v_reuseFailAlloc_1969_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1965_);
                    v___x_1967_ = v___x_1962_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1968_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
                    v___x_1967_ = v_reuseFailAlloc_1968_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1967_;
            }
            5 => {
                if v_isShared_1974_ == 0 {
                    v___x_1976_ = v___x_1973_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
                    v___x_1976_ = v_reuseFailAlloc_1977_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC___boxed(
    mut v_decl_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
    mut v_a_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1986_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_Decl_coalesceRC(
        v_decl_1980_,
        v_a_1981_,
        v_a_1982_,
        v_a_1983_,
        v_a_1984_,
    );
    crate::leanh::lean_dec(v_a_1984_);
    crate::leanh::lean_dec_ref(v_a_1983_);
    crate::leanh::lean_dec(v_a_1982_);
    crate::leanh::lean_dec_ref(v_a_1981_);
    return v_res_1986_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_coalesceRC___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1992_ = l_Lean_Compiler_LCNF_coalesceRC___closed__2;
    v___x_1993_ = 2;
    v___x_1994_ = l_Lean_Compiler_LCNF_coalesceRC___closed__1;
    v___x_1995_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_1994_,
        v___x_1993_,
        v___x_1992_,
        v___x_1991_,
    );
    return v___x_1995_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_coalesceRC() -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1996_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_coalesceRC___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_coalesceRC___closed__3_once),
        _init_l_Lean_Compiler_LCNF_coalesceRC___closed__3,
    );
    return v___x_1996_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = crate::leanh::lean_unsigned_to_nat(3124848603);
    v___x_2053_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
    v___x_2054_ = l_Lean_Name_num___override(v___x_2053_, v___x_2052_);
    return v___x_2054_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
    v___x_2057_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
    v___x_2058_ = l_Lean_Name_str___override(v___x_2057_, v___x_2056_);
    return v___x_2058_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2060_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
    v___x_2061_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
    v___x_2062_ = l_Lean_Name_str___override(v___x_2061_, v___x_2060_);
    return v___x_2062_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2064_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
    v___x_2065_ = l_Lean_Name_num___override(v___x_2064_, v___x_2063_);
    return v___x_2065_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_;
    v___x_2068_ = 1;
    v___x_2069_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_);
    v___x_2070_ = l_Lean_registerTraceClass(v___x_2067_, v___x_2068_, v___x_2069_);
    return v___x_2070_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2____boxed(
    mut v_a_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2072_ = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_();
    return v_res_2072_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_CoalesceRC(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_coalesceRC = _init_l_Lean_Compiler_LCNF_coalesceRC();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_coalesceRC);
    res = l___private_Lean_Compiler_LCNF_CoalesceRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_CoalesceRC_3124848603____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_CoalesceRC(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_CoalesceRC(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
}
