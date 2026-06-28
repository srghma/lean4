// Lean compiler output
// Module: Lean.Compiler.LCNF.PushProj
// Imports: Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Internalize
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Code_collectUsed, l_Lean_Compiler_LCNF_CodeDecl_collectUsed,
    l_Lean_Compiler_LCNF_attachCodeDecls, l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg;
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize, l_Lean_Compiler_LCNF_Decl_internalize,
    runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash, l_Lean_instInhabitedFVarIdHashSet,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_pushProj___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [112, 117, 115, 104, 80, 114, 111, 106, 0],
    };
static mut l_Lean_Compiler_LCNF_pushProj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pushProj___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4906690443001084389 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_pushProj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pushProj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_pushProj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__0_value) as *mut crate::leanh::LeanObject,6002029543643796387 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 117, 115, 104, 80, 114, 111, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1790360179806483262 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9410697049790244999 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9338128937441115898 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5262479513608925480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14794927585209949633 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7175746045895695224 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4801555735692583369 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16516678141487640844 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6161148531420215382 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14462547702771714495 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14594966017329367672 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1777867010 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,18309865256079098078 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2769903573489266121 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,361694778570169441 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14425366255458452540 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(
    mut v_alt_876_: *mut crate::leanh::LeanObject,
    mut v_f_877_: *mut crate::leanh::LeanObject,
    mut v___y_878_: *mut crate::leanh::LeanObject,
    mut v___y_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_894_: u8 = 0;
    let mut v_a_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut v_code_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_alt_876_) {
                0 => {
                    v_code_903_ = crate::leanh::lean_ctor_get(v_alt_876_, 2);
                    crate::leanh::lean_inc_ref(v_code_903_);
                    v___y_884_ = v_code_903_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_904_ = crate::leanh::lean_ctor_get(v_alt_876_, 1);
                    crate::leanh::lean_inc_ref(v_code_904_);
                    v___y_884_ = v_code_904_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_905_ = crate::leanh::lean_ctor_get(v_alt_876_, 0);
                    crate::leanh::lean_inc_ref(v_code_905_);
                    v___y_884_ = v_code_905_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                crate::leanh::lean_inc(v___y_881_);
                crate::leanh::lean_inc_ref(v___y_880_);
                crate::leanh::lean_inc(v___y_879_);
                crate::leanh::lean_inc_ref(v___y_878_);
                v___x_885_ = crate::leanh::lean_apply_6(
                    v_f_877_,
                    v___y_884_,
                    v___y_878_,
                    v___y_879_,
                    v___y_880_,
                    v___y_881_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_885_) == 0 {
                    v_a_886_ = crate::leanh::lean_ctor_get(v___x_885_, 0);
                    v_isSharedCheck_894_ = (!crate::leanh::lean_is_exclusive(v___x_885_)) as u8;
                    if v_isSharedCheck_894_ == 0 {
                        v___x_888_ = v___x_885_;
                        v_isShared_889_ = v_isSharedCheck_894_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_886_);
                        crate::leanh::lean_dec(v___x_885_);
                        v___x_888_ = crate::leanh::lean_box(0);
                        v_isShared_889_ = v_isSharedCheck_894_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_alt_876_);
                    v_a_895_ = crate::leanh::lean_ctor_get(v___x_885_, 0);
                    v_isSharedCheck_902_ = (!crate::leanh::lean_is_exclusive(v___x_885_)) as u8;
                    if v_isSharedCheck_902_ == 0 {
                        v___x_897_ = v___x_885_;
                        v_isShared_898_ = v_isSharedCheck_902_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_895_);
                        crate::leanh::lean_dec(v___x_885_);
                        v___x_897_ = crate::leanh::lean_box(0);
                        v_isShared_898_ = v_isSharedCheck_902_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_890_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_876_, v_a_886_);
                if v_isShared_889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_888_, 0, v___x_890_);
                    v___x_892_ = v___x_888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
                    v___x_892_ = v_reuseFailAlloc_893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_892_;
            }
            4 => {
                if v_isShared_898_ == 0 {
                    v___x_900_ = v___x_897_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
                    v___x_900_ = v_reuseFailAlloc_901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg___boxed(
    mut v_alt_906_: *mut crate::leanh::LeanObject,
    mut v_f_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: *mut crate::leanh::LeanObject,
    mut v___y_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_913_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_alt_906_, v_f_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
    crate::leanh::lean_dec(v___y_911_);
    crate::leanh::lean_dec_ref(v___y_910_);
    crate::leanh::lean_dec(v___y_909_);
    crate::leanh::lean_dec_ref(v___y_908_);
    return v_res_913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1(
    mut v_pu_914_: u8,
    mut v_alt_915_: *mut crate::leanh::LeanObject,
    mut v_f_916_: *mut crate::leanh::LeanObject,
    mut v___y_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
    mut v___y_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_922_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_alt_915_, v_f_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
    return v___x_922_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___boxed(
    mut v_pu_923_: *mut crate::leanh::LeanObject,
    mut v_alt_924_: *mut crate::leanh::LeanObject,
    mut v_f_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_931_: u8 = 0;
    let mut v_res_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_931_ = (crate::leanh::lean_unbox(v_pu_923_) as u8);
    v_res_932_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1(v_pu_boxed_931_, v_alt_924_, v_f_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
    crate::leanh::lean_dec(v___y_929_);
    crate::leanh::lean_dec_ref(v___y_928_);
    crate::leanh::lean_dec(v___y_927_);
    crate::leanh::lean_dec_ref(v___y_926_);
    return v_res_932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_x_934_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_935_: u8 = 0;
    let mut v_key_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_934_) == 0 {
                    v___x_935_ = 0;
                    return v___x_935_;
                } else {
                    v_key_936_ = crate::leanh::lean_ctor_get(v_x_934_, 0);
                    v_tail_937_ = crate::leanh::lean_ctor_get(v_x_934_, 2);
                    v___x_938_ = l_Lean_instBEqFVarId_beq(v_key_936_, v_a_933_);
                    if v___x_938_ == 0 {
                        v_x_934_ = v_tail_937_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_938_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg___boxed(
    mut v_a_940_: *mut crate::leanh::LeanObject,
    mut v_x_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_942_: u8 = 0;
    let mut v_r_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_940_, v_x_941_);
    crate::leanh::lean_dec(v_x_941_);
    crate::leanh::lean_dec(v_a_940_);
    v_r_943_ = crate::leanh::lean_box((v_res_942_) as usize);
    return v_r_943_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(
    mut v_m_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u64 = 0;
    let mut v___x_949_: u64 = 0;
    let mut v___x_950_: u64 = 0;
    let mut v_fold_951_: u64 = 0;
    let mut v___x_952_: u64 = 0;
    let mut v___x_953_: u64 = 0;
    let mut v___x_954_: u64 = 0;
    let mut v___x_955_: usize = 0;
    let mut v___x_956_: usize = 0;
    let mut v___x_957_: usize = 0;
    let mut v___x_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u8 = 0;
    v_buckets_946_ = crate::leanh::lean_ctor_get(v_m_944_, 1);
    v___x_947_ = lean_array_get_size(v_buckets_946_);
    v___x_948_ = l_Lean_instHashableFVarId_hash(v_a_945_);
    v___x_949_ = 32u64;
    v___x_950_ = lean_uint64_shift_right(v___x_948_, v___x_949_);
    v_fold_951_ = lean_uint64_xor(v___x_948_, v___x_950_);
    v___x_952_ = 16u64;
    v___x_953_ = lean_uint64_shift_right(v_fold_951_, v___x_952_);
    v___x_954_ = lean_uint64_xor(v_fold_951_, v___x_953_);
    v___x_955_ = lean_uint64_to_usize(v___x_954_);
    v___x_956_ = lean_usize_of_nat(v___x_947_);
    v___x_957_ = 1usize;
    v___x_958_ = lean_usize_sub(v___x_956_, v___x_957_);
    v___x_959_ = lean_usize_land(v___x_955_, v___x_958_);
    v___x_960_ = lean_array_uget_borrowed(v_buckets_946_, v___x_959_);
    v___x_961_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_945_, v___x_960_);
    return v___x_961_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg___boxed(
    mut v_m_962_: *mut crate::leanh::LeanObject,
    mut v_a_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_964_: u8 = 0;
    let mut v_r_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_964_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_962_, v_a_963_);
    crate::leanh::lean_dec(v_a_963_);
    crate::leanh::lean_dec_ref(v_m_962_);
    v_r_965_ = crate::leanh::lean_box((v_res_964_) as usize);
    return v_r_965_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(
    mut v_altsUsed_966_: *mut crate::leanh::LeanObject,
    mut v_j_967_: *mut crate::leanh::LeanObject,
    mut v_fvar_968_: *mut crate::leanh::LeanObject,
    mut v_b_969_: *mut crate::leanh::LeanObject,
    mut v___x_970_: u8,
    mut v_k_971_: *mut crate::leanh::LeanObject,
    mut v___y_972_: *mut crate::leanh::LeanObject,
    mut v___y_973_: *mut crate::leanh::LeanObject,
    mut v___y_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    v___x_977_ = l_Lean_instInhabitedFVarIdHashSet;
    v___x_978_ = lean_array_get_borrowed(v___x_977_, v_altsUsed_966_, v_j_967_);
    v___x_979_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v___x_978_, v_fvar_968_);
    if v___x_979_ == 0 {
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_b_969_);
        v___x_980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_980_, 0, v_k_971_);
        return v___x_980_;
    } else {
        let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_981_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_982_ = lean_mk_empty_array_with_capacity(v___x_981_);
        v___x_983_ = lean_array_push(v___x_982_, v_b_969_);
        v___x_984_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_970_, v___x_983_, v_k_971_);
        crate::leanh::lean_dec_ref(v___x_983_);
        v___x_985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_985_, 0, v___x_984_);
        return v___x_985_;
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed(
    mut v_altsUsed_986_: *mut crate::leanh::LeanObject,
    mut v_j_987_: *mut crate::leanh::LeanObject,
    mut v_fvar_988_: *mut crate::leanh::LeanObject,
    mut v_b_989_: *mut crate::leanh::LeanObject,
    mut v___x_990_: *mut crate::leanh::LeanObject,
    mut v_k_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
    mut v___y_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
    mut v___y_995_: *mut crate::leanh::LeanObject,
    mut v___y_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2347__boxed_997_: u8 = 0;
    let mut v_res_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2347__boxed_997_ = (crate::leanh::lean_unbox(v___x_990_) as u8);
    v_res_998_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(v_altsUsed_986_, v_j_987_, v_fvar_988_, v_b_989_, v___x_2347__boxed_997_, v_k_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
    crate::leanh::lean_dec(v___y_995_);
    crate::leanh::lean_dec_ref(v___y_994_);
    crate::leanh::lean_dec(v___y_993_);
    crate::leanh::lean_dec_ref(v___y_992_);
    crate::leanh::lean_dec(v_fvar_988_);
    crate::leanh::lean_dec(v_j_987_);
    crate::leanh::lean_dec_ref(v_altsUsed_986_);
    return v_res_998_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(
    mut v_altsUsed_999_: *mut crate::leanh::LeanObject,
    mut v_fvar_1000_: *mut crate::leanh::LeanObject,
    mut v_b_1001_: *mut crate::leanh::LeanObject,
    mut v_as_1002_: *mut crate::leanh::LeanObject,
    mut v_i_1003_: *mut crate::leanh::LeanObject,
    mut v_j_1004_: *mut crate::leanh::LeanObject,
    mut v_bs_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
    mut v___y_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1012_: u8 = 0;
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1028_: u8 = 0;
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1011_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1012_ = lean_nat_dec_eq(v_i_1003_, v_zero_1011_);
                if v_isZero_1012_ == 1 {
                    crate::leanh::lean_dec(v_j_1004_);
                    crate::leanh::lean_dec(v_i_1003_);
                    crate::leanh::lean_dec_ref(v_b_1001_);
                    crate::leanh::lean_dec(v_fvar_1000_);
                    crate::leanh::lean_dec_ref(v_altsUsed_999_);
                    v___x_1013_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1013_, 0, v_bs_1005_);
                    return v___x_1013_;
                } else {
                    v___x_1014_ = 1;
                    v___x_1015_ = crate::leanh::lean_box((v___x_1014_) as usize);
                    crate::leanh::lean_inc_ref(v_b_1001_);
                    crate::leanh::lean_inc(v_fvar_1000_);
                    crate::leanh::lean_inc(v_j_1004_);
                    crate::leanh::lean_inc_ref(v_altsUsed_999_);
                    v___f_1016_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                    crate::leanh::lean_closure_set(v___f_1016_, 0, v_altsUsed_999_);
                    crate::leanh::lean_closure_set(v___f_1016_, 1, v_j_1004_);
                    crate::leanh::lean_closure_set(v___f_1016_, 2, v_fvar_1000_);
                    crate::leanh::lean_closure_set(v___f_1016_, 3, v_b_1001_);
                    crate::leanh::lean_closure_set(v___f_1016_, 4, v___x_1015_);
                    v___x_1017_ = lean_array_fget_borrowed(v_as_1002_, v_j_1004_);
                    crate::leanh::lean_inc(v___x_1017_);
                    v___x_1018_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v___x_1017_, v___f_1016_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
                    if crate::leanh::lean_obj_tag(v___x_1018_) == 0 {
                        v_a_1019_ = crate::leanh::lean_ctor_get(v___x_1018_, 0);
                        crate::leanh::lean_inc(v_a_1019_);
                        crate::leanh::lean_dec_ref_known(v___x_1018_, 1);
                        v_one_1020_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1021_ = lean_nat_sub(v_i_1003_, v_one_1020_);
                        crate::leanh::lean_dec(v_i_1003_);
                        v___x_1022_ = lean_nat_add(v_j_1004_, v_one_1020_);
                        crate::leanh::lean_dec(v_j_1004_);
                        v___x_1023_ = lean_array_push(v_bs_1005_, v_a_1019_);
                        v_i_1003_ = v_n_1021_;
                        v_j_1004_ = v___x_1022_;
                        v_bs_1005_ = v___x_1023_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1005_);
                        crate::leanh::lean_dec(v_j_1004_);
                        crate::leanh::lean_dec(v_i_1003_);
                        crate::leanh::lean_dec_ref(v_b_1001_);
                        crate::leanh::lean_dec(v_fvar_1000_);
                        crate::leanh::lean_dec_ref(v_altsUsed_999_);
                        v_a_1025_ = crate::leanh::lean_ctor_get(v___x_1018_, 0);
                        v_isSharedCheck_1032_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1018_)) as u8;
                        if v_isSharedCheck_1032_ == 0 {
                            v___x_1027_ = v___x_1018_;
                            v_isShared_1028_ = v_isSharedCheck_1032_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1025_);
                            crate::leanh::lean_dec(v___x_1018_);
                            v___x_1027_ = crate::leanh::lean_box(0);
                            v_isShared_1028_ = v_isSharedCheck_1032_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1028_ == 0 {
                    v___x_1030_ = v___x_1027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
                    v___x_1030_ = v_reuseFailAlloc_1031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___boxed(
    mut v_altsUsed_1033_: *mut crate::leanh::LeanObject,
    mut v_fvar_1034_: *mut crate::leanh::LeanObject,
    mut v_b_1035_: *mut crate::leanh::LeanObject,
    mut v_as_1036_: *mut crate::leanh::LeanObject,
    mut v_i_1037_: *mut crate::leanh::LeanObject,
    mut v_j_1038_: *mut crate::leanh::LeanObject,
    mut v_bs_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
    mut v___y_1041_: *mut crate::leanh::LeanObject,
    mut v___y_1042_: *mut crate::leanh::LeanObject,
    mut v___y_1043_: *mut crate::leanh::LeanObject,
    mut v___y_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_1033_, v_fvar_1034_, v_b_1035_, v_as_1036_, v_i_1037_, v_j_1038_, v_bs_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
    crate::leanh::lean_dec(v___y_1043_);
    crate::leanh::lean_dec_ref(v___y_1042_);
    crate::leanh::lean_dec(v___y_1041_);
    crate::leanh::lean_dec_ref(v___y_1040_);
    crate::leanh::lean_dec_ref(v_as_1036_);
    return v_res_1045_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(
    mut v_fvar_1046_: *mut crate::leanh::LeanObject,
    mut v_b_1047_: *mut crate::leanh::LeanObject,
    mut v_sz_1048_: usize,
    mut v_i_1049_: usize,
    mut v_bs_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: u8 = 0;
    let mut v_v_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: usize = 0;
    let mut v___x_1058_: usize = 0;
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: u8 = 0;
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1051_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
                if v___x_1051_ == 0 {
                    crate::leanh::lean_dec_ref(v_b_1047_);
                    return v_bs_1050_;
                } else {
                    v_v_1052_ = lean_array_uget(v_bs_1050_, v_i_1049_);
                    v___x_1053_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1054_ = lean_array_uset(v_bs_1050_, v_i_1049_, v___x_1053_);
                    v___x_1061_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_v_1052_, v_fvar_1046_);
                    if v___x_1061_ == 0 {
                        v___y_1056_ = v_v_1052_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1062_ = 1;
                        crate::leanh::lean_inc_ref(v_b_1047_);
                        v___x_1063_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(
                            v___x_1062_,
                            v_b_1047_,
                            v_v_1052_,
                        );
                        v___y_1056_ = v___x_1063_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1057_ = 1usize;
                v___x_1058_ = lean_usize_add(v_i_1049_, v___x_1057_);
                v___x_1059_ = lean_array_uset(v_bs_x27_1054_, v_i_1049_, v___y_1056_);
                v_i_1049_ = v___x_1058_;
                v_bs_1050_ = v___x_1059_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3___boxed(
    mut v_fvar_1064_: *mut crate::leanh::LeanObject,
    mut v_b_1065_: *mut crate::leanh::LeanObject,
    mut v_sz_1066_: *mut crate::leanh::LeanObject,
    mut v_i_1067_: *mut crate::leanh::LeanObject,
    mut v_bs_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1069_: usize = 0;
    let mut v_i_boxed_1070_: usize = 0;
    let mut v_res_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1069_ = crate::leanh::lean_unbox_usize(v_sz_1066_);
    crate::leanh::lean_dec(v_sz_1066_);
    v_i_boxed_1070_ = crate::leanh::lean_unbox_usize(v_i_1067_);
    crate::leanh::lean_dec(v_i_1067_);
    v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v_fvar_1064_, v_b_1065_, v_sz_boxed_1069_, v_i_boxed_1070_, v_bs_1068_);
    crate::leanh::lean_dec(v_fvar_1064_);
    return v_res_1071_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = 1;
    v___x_1073_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(
    mut v_decls_1074_: *mut crate::leanh::LeanObject,
    mut v_alts_1075_: *mut crate::leanh::LeanObject,
    mut v_altsUsed_1076_: *mut crate::leanh::LeanObject,
    mut v_ctx_1077_: *mut crate::leanh::LeanObject,
    mut v_ctxUsed_1078_: *mut crate::leanh::LeanObject,
    mut v_a_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1103_: usize = 0;
    let mut v___x_1104_: usize = 0;
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvar_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut v_unused_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1084_ = lean_array_get_size(v_decls_1074_);
                v___x_1085_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1086_ = lean_nat_dec_eq(v___x_1084_, v___x_1085_);
                if v___x_1086_ == 0 {
                    v___x_1087_ = 1;
                    v___x_1088_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0);
                    v___x_1089_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1090_ = lean_nat_sub(v___x_1084_, v___x_1089_);
                    v_b_1091_ = lean_array_get(v___x_1088_, v_decls_1074_, v___x_1090_);
                    crate::leanh::lean_dec(v___x_1090_);
                    v_bs_1092_ = lean_array_pop(v_decls_1074_);
                    crate::leanh::lean_inc(v_b_1091_);
                    crate::leanh::lean_inc_ref(v_bs_1092_);
                    v___x_1115_ = lean_array_push(v_bs_1092_, v_b_1091_);
                    crate::leanh::lean_inc_ref(v_ctx_1077_);
                    v___x_1116_ = l_Array_reverse___redArg(v_ctx_1077_);
                    v___x_1117_ = l_Array_append___redArg(v___x_1115_, v___x_1116_);
                    crate::leanh::lean_dec_ref(v___x_1116_);
                    crate::leanh::lean_inc_ref(v_alts_1075_);
                    v___x_1118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1117_);
                    crate::leanh::lean_ctor_set(v___x_1118_, 1, v_alts_1075_);
                    if crate::leanh::lean_obj_tag(v_b_1091_) == 0 {
                        v_decl_1119_ = crate::leanh::lean_ctor_get(v_b_1091_, 0);
                        v_fvarId_1120_ = crate::leanh::lean_ctor_get(v_decl_1119_, 0);
                        v_value_1121_ = crate::leanh::lean_ctor_get(v_decl_1119_, 3);
                        crate::leanh::lean_inc_ref_n(v_b_1091_, 2);
                        crate::leanh::lean_inc_ref(v_ctx_1077_);
                        v___x_1122_ = lean_array_push(v_ctx_1077_, v_b_1091_);
                        crate::leanh::lean_inc_ref(v_ctxUsed_1078_);
                        v___x_1123_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(
                            v___x_1087_,
                            v_b_1091_,
                            v_ctxUsed_1078_,
                        );
                        match crate::leanh::lean_obj_tag(v_value_1121_) {
                            7 => {
                                crate::leanh::lean_dec_ref_known(v___x_1118_, 2);
                                crate::leanh::lean_inc(v_fvarId_1120_);
                                v_fvar_1125_ = v_fvarId_1120_;
                                v___y_1126_ = v_a_1079_;
                                v___y_1127_ = v_a_1080_;
                                v___y_1128_ = v_a_1081_;
                                v___y_1129_ = v_a_1082_;
                                state = 4;
                                continue;
                            }
                            6 => {
                                crate::leanh::lean_dec_ref_known(v___x_1118_, 2);
                                crate::leanh::lean_inc(v_fvarId_1120_);
                                v_fvar_1125_ = v_fvarId_1120_;
                                v___y_1126_ = v_a_1079_;
                                v___y_1127_ = v_a_1080_;
                                v___y_1128_ = v_a_1081_;
                                v___y_1129_ = v_a_1082_;
                                state = 4;
                                continue;
                            }
                            8 => {
                                crate::leanh::lean_dec_ref_known(v___x_1118_, 2);
                                crate::leanh::lean_inc(v_fvarId_1120_);
                                v_fvar_1125_ = v_fvarId_1120_;
                                v___y_1126_ = v_a_1079_;
                                v___y_1127_ = v_a_1080_;
                                v___y_1128_ = v_a_1081_;
                                v___y_1129_ = v_a_1082_;
                                state = 4;
                                continue;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref(v___x_1123_);
                                crate::leanh::lean_dec_ref(v___x_1122_);
                                crate::leanh::lean_dec_ref(v_bs_1092_);
                                crate::leanh::lean_dec_ref(v_ctxUsed_1078_);
                                crate::leanh::lean_dec_ref(v_ctx_1077_);
                                crate::leanh::lean_dec_ref(v_altsUsed_1076_);
                                crate::leanh::lean_dec_ref(v_alts_1075_);
                                v_isSharedCheck_1138_ =
                                    (!crate::leanh::lean_is_exclusive(v_b_1091_)) as u8;
                                if v_isSharedCheck_1138_ == 0 {
                                    v_unused_1139_ = crate::leanh::lean_ctor_get(v_b_1091_, 0);
                                    crate::leanh::lean_dec(v_unused_1139_);
                                    v___x_1133_ = v_b_1091_;
                                    v_isShared_1134_ = v_isSharedCheck_1138_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_b_1091_);
                                    v___x_1133_ = crate::leanh::lean_box(0);
                                    v_isShared_1134_ = v_isSharedCheck_1138_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1092_);
                        crate::leanh::lean_dec(v_b_1091_);
                        crate::leanh::lean_dec_ref(v_ctxUsed_1078_);
                        crate::leanh::lean_dec_ref(v_ctx_1077_);
                        crate::leanh::lean_dec_ref(v_altsUsed_1076_);
                        crate::leanh::lean_dec_ref(v_alts_1075_);
                        v___x_1140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1140_, 0, v___x_1118_);
                        return v___x_1140_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctxUsed_1078_);
                    crate::leanh::lean_dec_ref(v_altsUsed_1076_);
                    crate::leanh::lean_dec_ref(v_decls_1074_);
                    v___x_1141_ = l_Array_reverse___redArg(v_ctx_1077_);
                    v___x_1142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1142_, 0, v___x_1141_);
                    crate::leanh::lean_ctor_set(v___x_1142_, 1, v_alts_1075_);
                    v___x_1143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                    return v___x_1143_;
                }
            }
            1 => {
                v___x_1099_ = lean_array_get_size(v_alts_1075_);
                v___x_1100_ = lean_mk_empty_array_with_capacity(v___x_1099_);
                crate::leanh::lean_inc(v_b_1091_);
                crate::leanh::lean_inc(v___y_1094_);
                crate::leanh::lean_inc_ref(v_altsUsed_1076_);
                v___x_1101_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_1076_, v___y_1094_, v_b_1091_, v_alts_1075_, v___x_1099_, v___x_1085_, v___x_1100_, v___y_1097_, v___y_1098_, v___y_1096_, v___y_1095_);
                crate::leanh::lean_dec_ref(v_alts_1075_);
                if crate::leanh::lean_obj_tag(v___x_1101_) == 0 {
                    v_a_1102_ = crate::leanh::lean_ctor_get(v___x_1101_, 0);
                    crate::leanh::lean_inc(v_a_1102_);
                    crate::leanh::lean_dec_ref_known(v___x_1101_, 1);
                    v_sz_1103_ = lean_array_size(v_altsUsed_1076_);
                    v___x_1104_ = 0usize;
                    v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v___y_1094_, v_b_1091_, v_sz_1103_, v___x_1104_, v_altsUsed_1076_);
                    crate::leanh::lean_dec(v___y_1094_);
                    v_decls_1074_ = v_bs_1092_;
                    v_alts_1075_ = v_a_1102_;
                    v_altsUsed_1076_ = v___x_1105_;
                    v_a_1079_ = v___y_1097_;
                    v_a_1080_ = v___y_1098_;
                    v_a_1081_ = v___y_1096_;
                    v_a_1082_ = v___y_1095_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1094_);
                    crate::leanh::lean_dec_ref(v_bs_1092_);
                    crate::leanh::lean_dec(v_b_1091_);
                    crate::leanh::lean_dec_ref(v_ctxUsed_1078_);
                    crate::leanh::lean_dec_ref(v_ctx_1077_);
                    crate::leanh::lean_dec_ref(v_altsUsed_1076_);
                    v_a_1107_ = crate::leanh::lean_ctor_get(v___x_1101_, 0);
                    v_isSharedCheck_1114_ = (!crate::leanh::lean_is_exclusive(v___x_1101_)) as u8;
                    if v_isSharedCheck_1114_ == 0 {
                        v___x_1109_ = v___x_1101_;
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1107_);
                        crate::leanh::lean_dec(v___x_1101_);
                        v___x_1109_ = crate::leanh::lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1110_ == 0 {
                    v___x_1112_ = v___x_1109_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
                    v___x_1112_ = v_reuseFailAlloc_1113_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1112_;
            }
            4 => {
                v___x_1130_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_ctxUsed_1078_, v_fvar_1125_);
                if v___x_1130_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1123_);
                    crate::leanh::lean_dec_ref(v___x_1122_);
                    v___y_1094_ = v_fvar_1125_;
                    v___y_1095_ = v___y_1129_;
                    v___y_1096_ = v___y_1128_;
                    v___y_1097_ = v___y_1126_;
                    v___y_1098_ = v___y_1127_;
                    state = 1;
                    continue;
                } else {
                    if v___x_1086_ == 0 {
                        crate::leanh::lean_dec(v_fvar_1125_);
                        crate::leanh::lean_dec_ref_known(v_b_1091_, 1);
                        crate::leanh::lean_dec_ref(v_ctxUsed_1078_);
                        crate::leanh::lean_dec_ref(v_ctx_1077_);
                        v_decls_1074_ = v_bs_1092_;
                        v_ctx_1077_ = v___x_1122_;
                        v_ctxUsed_1078_ = v___x_1123_;
                        v_a_1079_ = v___y_1126_;
                        v_a_1080_ = v___y_1127_;
                        v_a_1081_ = v___y_1128_;
                        v_a_1082_ = v___y_1129_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1123_);
                        crate::leanh::lean_dec_ref(v___x_1122_);
                        v___y_1094_ = v_fvar_1125_;
                        v___y_1095_ = v___y_1129_;
                        v___y_1096_ = v___y_1128_;
                        v___y_1097_ = v___y_1126_;
                        v___y_1098_ = v___y_1127_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1134_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1118_);
                    v___x_1136_ = v___x_1133_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1118_);
                    v___x_1136_ = v_reuseFailAlloc_1137_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___boxed(
    mut v_decls_1144_: *mut crate::leanh::LeanObject,
    mut v_alts_1145_: *mut crate::leanh::LeanObject,
    mut v_altsUsed_1146_: *mut crate::leanh::LeanObject,
    mut v_ctx_1147_: *mut crate::leanh::LeanObject,
    mut v_ctxUsed_1148_: *mut crate::leanh::LeanObject,
    mut v_a_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(
        v_decls_1144_,
        v_alts_1145_,
        v_altsUsed_1146_,
        v_ctx_1147_,
        v_ctxUsed_1148_,
        v_a_1149_,
        v_a_1150_,
        v_a_1151_,
        v_a_1152_,
    );
    crate::leanh::lean_dec(v_a_1152_);
    crate::leanh::lean_dec_ref(v_a_1151_);
    crate::leanh::lean_dec(v_a_1150_);
    crate::leanh::lean_dec_ref(v_a_1149_);
    return v_res_1154_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(
    mut v_00_u03b2_1155_: *mut crate::leanh::LeanObject,
    mut v_m_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1158_: u8 = 0;
    v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_1156_, v_a_1157_);
    return v___x_1158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___boxed(
    mut v_00_u03b2_1159_: *mut crate::leanh::LeanObject,
    mut v_m_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1162_: u8 = 0;
    let mut v_r_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(v_00_u03b2_1159_, v_m_1160_, v_a_1161_);
    crate::leanh::lean_dec(v_a_1161_);
    crate::leanh::lean_dec_ref(v_m_1160_);
    v_r_1163_ = crate::leanh::lean_box((v_res_1162_) as usize);
    return v_r_1163_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(
    mut v_altsUsed_1164_: *mut crate::leanh::LeanObject,
    mut v_fvar_1165_: *mut crate::leanh::LeanObject,
    mut v_b_1166_: *mut crate::leanh::LeanObject,
    mut v_as_1167_: *mut crate::leanh::LeanObject,
    mut v_i_1168_: *mut crate::leanh::LeanObject,
    mut v_j_1169_: *mut crate::leanh::LeanObject,
    mut v_inv_1170_: *mut crate::leanh::LeanObject,
    mut v_bs_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_1164_, v_fvar_1165_, v_b_1166_, v_as_1167_, v_i_1168_, v_j_1169_, v_bs_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
    return v___x_1177_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___boxed(
    mut v_altsUsed_1178_: *mut crate::leanh::LeanObject,
    mut v_fvar_1179_: *mut crate::leanh::LeanObject,
    mut v_b_1180_: *mut crate::leanh::LeanObject,
    mut v_as_1181_: *mut crate::leanh::LeanObject,
    mut v_i_1182_: *mut crate::leanh::LeanObject,
    mut v_j_1183_: *mut crate::leanh::LeanObject,
    mut v_inv_1184_: *mut crate::leanh::LeanObject,
    mut v_bs_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(v_altsUsed_1178_, v_fvar_1179_, v_b_1180_, v_as_1181_, v_i_1182_, v_j_1183_, v_inv_1184_, v_bs_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
    crate::leanh::lean_dec(v___y_1189_);
    crate::leanh::lean_dec_ref(v___y_1188_);
    crate::leanh::lean_dec(v___y_1187_);
    crate::leanh::lean_dec_ref(v___y_1186_);
    crate::leanh::lean_dec_ref(v_as_1181_);
    return v_res_1191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(
    mut v_00_u03b2_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_x_1194_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1195_: u8 = 0;
    v___x_1195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_1193_, v_x_1194_);
    return v___x_1195_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_x_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1199_: u8 = 0;
    let mut v_r_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(v_00_u03b2_1196_, v_a_1197_, v_x_1198_);
    crate::leanh::lean_dec(v_x_1198_);
    crate::leanh::lean_dec(v_a_1197_);
    v_r_1200_ = crate::leanh::lean_box((v_res_1199_) as usize);
    return v_r_1200_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(
    mut v_sz_1201_: usize,
    mut v_i_1202_: usize,
    mut v_bs_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: u8 = 0;
    let mut v___y_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: usize = 0;
    let mut v___x_1214_: usize = 0;
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1204_ = lean_usize_dec_lt(v_i_1202_, v_sz_1201_);
                if v___x_1204_ == 0 {
                    return v_bs_1203_;
                } else {
                    v___x_1205_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                    v_v_1206_ = lean_array_uget(v_bs_1203_, v_i_1202_);
                    v___x_1207_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1208_ = lean_array_uset(v_bs_1203_, v_i_1202_, v___x_1207_);
                    v___x_1209_ = 1;
                    match crate::leanh::lean_obj_tag(v_v_1206_) {
                        0 => {
                            v_code_1217_ = crate::leanh::lean_ctor_get(v_v_1206_, 2);
                            crate::leanh::lean_inc_ref(v_code_1217_);
                            crate::leanh::lean_dec_ref_known(v_v_1206_, 3);
                            v___y_1211_ = v_code_1217_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1218_ = crate::leanh::lean_ctor_get(v_v_1206_, 1);
                            crate::leanh::lean_inc_ref(v_code_1218_);
                            crate::leanh::lean_dec_ref_known(v_v_1206_, 2);
                            v___y_1211_ = v_code_1218_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1219_ = crate::leanh::lean_ctor_get(v_v_1206_, 0);
                            crate::leanh::lean_inc_ref(v_code_1219_);
                            crate::leanh::lean_dec_ref_known(v_v_1206_, 1);
                            v___y_1211_ = v_code_1219_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1212_ =
                    l_Lean_Compiler_LCNF_Code_collectUsed(v___x_1209_, v___y_1211_, v___x_1205_);
                v___x_1213_ = 1usize;
                v___x_1214_ = lean_usize_add(v_i_1202_, v___x_1213_);
                v___x_1215_ = lean_array_uset(v_bs_x27_1208_, v_i_1202_, v___x_1212_);
                v_i_1202_ = v___x_1214_;
                v_bs_1203_ = v___x_1215_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1___boxed(
    mut v_sz_1220_: *mut crate::leanh::LeanObject,
    mut v_i_1221_: *mut crate::leanh::LeanObject,
    mut v_bs_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1223_: usize = 0;
    let mut v_i_boxed_1224_: usize = 0;
    let mut v_res_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1223_ = crate::leanh::lean_unbox_usize(v_sz_1220_);
    crate::leanh::lean_dec(v_sz_1220_);
    v_i_boxed_1224_ = crate::leanh::lean_unbox_usize(v_i_1221_);
    crate::leanh::lean_dec(v_i_1221_);
    v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_boxed_1223_, v_i_boxed_1224_, v_bs_1222_);
    return v_res_1225_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_1226_: *mut crate::leanh::LeanObject,
    mut v_x_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: u64 = 0;
    let mut v___x_1236_: u64 = 0;
    let mut v___x_1237_: u64 = 0;
    let mut v_fold_1238_: u64 = 0;
    let mut v___x_1239_: u64 = 0;
    let mut v___x_1240_: u64 = 0;
    let mut v___x_1241_: u64 = 0;
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: usize = 0;
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1227_) == 0 {
                    return v_x_1226_;
                } else {
                    v_key_1228_ = crate::leanh::lean_ctor_get(v_x_1227_, 0);
                    v_value_1229_ = crate::leanh::lean_ctor_get(v_x_1227_, 1);
                    v_tail_1230_ = crate::leanh::lean_ctor_get(v_x_1227_, 2);
                    v_isSharedCheck_1253_ = (!crate::leanh::lean_is_exclusive(v_x_1227_)) as u8;
                    if v_isSharedCheck_1253_ == 0 {
                        v___x_1232_ = v_x_1227_;
                        v_isShared_1233_ = v_isSharedCheck_1253_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1230_);
                        crate::leanh::lean_inc(v_value_1229_);
                        crate::leanh::lean_inc(v_key_1228_);
                        crate::leanh::lean_dec(v_x_1227_);
                        v___x_1232_ = crate::leanh::lean_box(0);
                        v_isShared_1233_ = v_isSharedCheck_1253_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1234_ = lean_array_get_size(v_x_1226_);
                v___x_1235_ = l_Lean_instHashableFVarId_hash(v_key_1228_);
                v___x_1236_ = 32u64;
                v___x_1237_ = lean_uint64_shift_right(v___x_1235_, v___x_1236_);
                v_fold_1238_ = lean_uint64_xor(v___x_1235_, v___x_1237_);
                v___x_1239_ = 16u64;
                v___x_1240_ = lean_uint64_shift_right(v_fold_1238_, v___x_1239_);
                v___x_1241_ = lean_uint64_xor(v_fold_1238_, v___x_1240_);
                v___x_1242_ = lean_uint64_to_usize(v___x_1241_);
                v___x_1243_ = lean_usize_of_nat(v___x_1234_);
                v___x_1244_ = 1usize;
                v___x_1245_ = lean_usize_sub(v___x_1243_, v___x_1244_);
                v___x_1246_ = lean_usize_land(v___x_1242_, v___x_1245_);
                v___x_1247_ = lean_array_uget_borrowed(v_x_1226_, v___x_1246_);
                crate::leanh::lean_inc(v___x_1247_);
                if v_isShared_1233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1232_, 2, v___x_1247_);
                    v___x_1249_ = v___x_1232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_key_1228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_value_1229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 2, v___x_1247_);
                    v___x_1249_ = v_reuseFailAlloc_1252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1250_ = lean_array_uset(v_x_1226_, v___x_1246_, v___x_1249_);
                v_x_1226_ = v___x_1250_;
                v_x_1227_ = v_tail_1230_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(
    mut v_i_1254_: *mut crate::leanh::LeanObject,
    mut v_source_1255_: *mut crate::leanh::LeanObject,
    mut v_target_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: u8 = 0;
    let mut v_es_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1257_ = lean_array_get_size(v_source_1255_);
                v___x_1258_ = lean_nat_dec_lt(v_i_1254_, v___x_1257_);
                if v___x_1258_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1255_);
                    crate::leanh::lean_dec(v_i_1254_);
                    return v_target_1256_;
                } else {
                    v_es_1259_ = lean_array_fget(v_source_1255_, v_i_1254_);
                    v___x_1260_ = crate::leanh::lean_box(0);
                    v_source_1261_ = lean_array_fset(v_source_1255_, v_i_1254_, v___x_1260_);
                    v_target_1262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_target_1256_, v_es_1259_);
                    v___x_1263_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1264_ = lean_nat_add(v_i_1254_, v___x_1263_);
                    crate::leanh::lean_dec(v_i_1254_);
                    v_i_1254_ = v___x_1264_;
                    v_source_1255_ = v_source_1261_;
                    v_target_1256_ = v_target_1262_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(
    mut v_data_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = lean_array_get_size(v_data_1266_);
    v___x_1268_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1269_ = lean_nat_mul(v___x_1267_, v___x_1268_);
    v___x_1270_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1271_ = crate::leanh::lean_box(0);
    v___x_1272_ = lean_mk_array(v_nbuckets_1269_, v___x_1271_);
    v___x_1273_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v___x_1270_, v_data_1266_, v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(
    mut v_m_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_b_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u64 = 0;
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: u64 = 0;
    let mut v_fold_1283_: u64 = 0;
    let mut v___x_1284_: u64 = 0;
    let mut v___x_1285_: u64 = 0;
    let mut v___x_1286_: u64 = 0;
    let mut v___x_1287_: usize = 0;
    let mut v___x_1288_: usize = 0;
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: usize = 0;
    let mut v___x_1291_: usize = 0;
    let mut v_bkt_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v_val_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1314_: u8 = 0;
    let mut v_unused_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1277_ = crate::leanh::lean_ctor_get(v_m_1274_, 0);
                v_buckets_1278_ = crate::leanh::lean_ctor_get(v_m_1274_, 1);
                v___x_1279_ = lean_array_get_size(v_buckets_1278_);
                v___x_1280_ = l_Lean_instHashableFVarId_hash(v_a_1275_);
                v___x_1281_ = 32u64;
                v___x_1282_ = lean_uint64_shift_right(v___x_1280_, v___x_1281_);
                v_fold_1283_ = lean_uint64_xor(v___x_1280_, v___x_1282_);
                v___x_1284_ = 16u64;
                v___x_1285_ = lean_uint64_shift_right(v_fold_1283_, v___x_1284_);
                v___x_1286_ = lean_uint64_xor(v_fold_1283_, v___x_1285_);
                v___x_1287_ = lean_uint64_to_usize(v___x_1286_);
                v___x_1288_ = lean_usize_of_nat(v___x_1279_);
                v___x_1289_ = 1usize;
                v___x_1290_ = lean_usize_sub(v___x_1288_, v___x_1289_);
                v___x_1291_ = lean_usize_land(v___x_1287_, v___x_1290_);
                v_bkt_1292_ = lean_array_uget_borrowed(v_buckets_1278_, v___x_1291_);
                v___x_1293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_1275_, v_bkt_1292_);
                if v___x_1293_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1278_);
                    crate::leanh::lean_inc(v_size_1277_);
                    v_isSharedCheck_1314_ = (!crate::leanh::lean_is_exclusive(v_m_1274_)) as u8;
                    if v_isSharedCheck_1314_ == 0 {
                        v_unused_1315_ = crate::leanh::lean_ctor_get(v_m_1274_, 1);
                        crate::leanh::lean_dec(v_unused_1315_);
                        v_unused_1316_ = crate::leanh::lean_ctor_get(v_m_1274_, 0);
                        crate::leanh::lean_dec(v_unused_1316_);
                        v___x_1295_ = v_m_1274_;
                        v_isShared_1296_ = v_isSharedCheck_1314_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1274_);
                        v___x_1295_ = crate::leanh::lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1314_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1276_);
                    crate::leanh::lean_dec(v_a_1275_);
                    return v_m_1274_;
                }
            }
            1 => {
                v___x_1297_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1298_ = lean_nat_add(v_size_1277_, v___x_1297_);
                crate::leanh::lean_dec(v_size_1277_);
                crate::leanh::lean_inc(v_bkt_1292_);
                v___x_1299_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1299_, 0, v_a_1275_);
                crate::leanh::lean_ctor_set(v___x_1299_, 1, v_b_1276_);
                crate::leanh::lean_ctor_set(v___x_1299_, 2, v_bkt_1292_);
                v_buckets_x27_1300_ = lean_array_uset(v_buckets_1278_, v___x_1291_, v___x_1299_);
                v___x_1301_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1302_ = lean_nat_mul(v_size_x27_1298_, v___x_1301_);
                v___x_1303_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1304_ = lean_nat_div(v___x_1302_, v___x_1303_);
                crate::leanh::lean_dec(v___x_1302_);
                v___x_1305_ = lean_array_get_size(v_buckets_x27_1300_);
                v___x_1306_ = lean_nat_dec_le(v___x_1304_, v___x_1305_);
                crate::leanh::lean_dec(v___x_1304_);
                if v___x_1306_ == 0 {
                    v_val_1307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_buckets_x27_1300_);
                    if v_isShared_1296_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1295_, 1, v_val_1307_);
                        crate::leanh::lean_ctor_set(v___x_1295_, 0, v_size_x27_1298_);
                        v___x_1309_ = v___x_1295_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1310_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_size_x27_1298_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_val_1307_);
                        v___x_1309_ = v_reuseFailAlloc_1310_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1296_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1295_, 1, v_buckets_x27_1300_);
                        crate::leanh::lean_ctor_set(v___x_1295_, 0, v_size_x27_1298_);
                        v___x_1312_ = v___x_1295_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_size_x27_1298_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_buckets_x27_1300_);
                        v___x_1312_ = v_reuseFailAlloc_1313_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1309_;
            }
            3 => {
                return v___x_1312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed(
    mut v_code_1319_: *mut crate::leanh::LeanObject,
    mut v_a_1320_: *mut crate::leanh::LeanObject,
    mut v_a_1321_: *mut crate::leanh::LeanObject,
    mut v_a_1322_: *mut crate::leanh::LeanObject,
    mut v_a_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1325_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(
        v_code_1319_,
        v_a_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
    );
    crate::leanh::lean_dec(v_a_1323_);
    crate::leanh::lean_dec_ref(v_a_1322_);
    crate::leanh::lean_dec(v_a_1321_);
    crate::leanh::lean_dec_ref(v_a_1320_);
    return v_res_1325_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(
    mut v_i_1326_: *mut crate::leanh::LeanObject,
    mut v_as_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: usize = 0;
    let mut v___x_1341_: usize = 0;
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1353_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1333_ = lean_array_get_size(v_as_1327_);
                v___x_1334_ = lean_nat_dec_lt(v_i_1326_, v___x_1333_);
                if v___x_1334_ == 0 {
                    crate::leanh::lean_dec(v_i_1326_);
                    v___x_1335_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1335_, 0, v_as_1327_);
                    return v___x_1335_;
                } else {
                    v_a_1336_ = lean_array_fget_borrowed(v_as_1327_, v_i_1326_);
                    v___x_1337_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed as *mut core::ffi::c_void, 6, 0);
                    crate::leanh::lean_inc(v_a_1336_);
                    v___x_1338_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_a_1336_, v___x_1337_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
                    if crate::leanh::lean_obj_tag(v___x_1338_) == 0 {
                        v_a_1339_ = crate::leanh::lean_ctor_get(v___x_1338_, 0);
                        crate::leanh::lean_inc(v_a_1339_);
                        crate::leanh::lean_dec_ref_known(v___x_1338_, 1);
                        v___x_1340_ = lean_ptr_addr(v_a_1336_);
                        v___x_1341_ = lean_ptr_addr(v_a_1339_);
                        v___x_1342_ = lean_usize_dec_eq(v___x_1340_, v___x_1341_);
                        if v___x_1342_ == 0 {
                            v___x_1343_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1344_ = lean_nat_add(v_i_1326_, v___x_1343_);
                            v___x_1345_ = lean_array_fset(v_as_1327_, v_i_1326_, v_a_1339_);
                            crate::leanh::lean_dec(v_i_1326_);
                            v_i_1326_ = v___x_1344_;
                            v_as_1327_ = v___x_1345_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1339_);
                            v___x_1347_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1348_ = lean_nat_add(v_i_1326_, v___x_1347_);
                            crate::leanh::lean_dec(v_i_1326_);
                            v_i_1326_ = v___x_1348_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_1327_);
                        crate::leanh::lean_dec(v_i_1326_);
                        v_a_1350_ = crate::leanh::lean_ctor_get(v___x_1338_, 0);
                        v_isSharedCheck_1357_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1338_)) as u8;
                        if v_isSharedCheck_1357_ == 0 {
                            v___x_1352_ = v___x_1338_;
                            v_isShared_1353_ = v_isSharedCheck_1357_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1350_);
                            crate::leanh::lean_dec(v___x_1338_);
                            v___x_1352_ = crate::leanh::lean_box(0);
                            v_isShared_1353_ = v_isSharedCheck_1357_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1353_ == 0 {
                    v___x_1355_ = v___x_1352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
                    v___x_1355_ = v_reuseFailAlloc_1356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(
    mut v_c_1358_: *mut crate::leanh::LeanObject,
    mut v_decls_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeName_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1371_: u8 = 0;
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1373_: usize = 0;
    let mut v___x_1374_: usize = 0;
    let mut v_altsUsed_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctxUsed_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v___x_1389_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_a_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_a_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_1365_ = crate::leanh::lean_ctor_get(v_c_1358_, 0);
                v_resultType_1366_ = crate::leanh::lean_ctor_get(v_c_1358_, 1);
                v_discr_1367_ = crate::leanh::lean_ctor_get(v_c_1358_, 2);
                v_alts_1368_ = crate::leanh::lean_ctor_get(v_c_1358_, 3);
                v_isSharedCheck_1415_ = (!crate::leanh::lean_is_exclusive(v_c_1358_)) as u8;
                if v_isSharedCheck_1415_ == 0 {
                    v___x_1370_ = v_c_1358_;
                    v_isShared_1371_ = v_isSharedCheck_1415_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_alts_1368_);
                    crate::leanh::lean_inc(v_discr_1367_);
                    crate::leanh::lean_inc(v_resultType_1366_);
                    crate::leanh::lean_inc(v_typeName_1365_);
                    crate::leanh::lean_dec(v_c_1358_);
                    v___x_1370_ = crate::leanh::lean_box(0);
                    v_isShared_1371_ = v_isSharedCheck_1415_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1372_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v_sz_1373_ = lean_array_size(v_alts_1368_);
                v___x_1374_ = 0usize;
                crate::leanh::lean_inc_ref(v_alts_1368_);
                v_altsUsed_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_1373_, v___x_1374_, v_alts_1368_);
                v___x_1376_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_discr_1367_);
                v_ctxUsed_1377_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v___x_1372_, v_discr_1367_, v___x_1376_);
                v___x_1378_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1379_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0;
                v___x_1380_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_1359_, v_alts_1368_, v_altsUsed_1375_, v___x_1379_, v_ctxUsed_1377_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
                if crate::leanh::lean_obj_tag(v___x_1380_) == 0 {
                    v_a_1381_ = crate::leanh::lean_ctor_get(v___x_1380_, 0);
                    crate::leanh::lean_inc(v_a_1381_);
                    crate::leanh::lean_dec_ref_known(v___x_1380_, 1);
                    v_fst_1382_ = crate::leanh::lean_ctor_get(v_a_1381_, 0);
                    crate::leanh::lean_inc(v_fst_1382_);
                    v_snd_1383_ = crate::leanh::lean_ctor_get(v_a_1381_, 1);
                    crate::leanh::lean_inc(v_snd_1383_);
                    crate::leanh::lean_dec(v_a_1381_);
                    v___x_1384_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v___x_1378_, v_snd_1383_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
                    if crate::leanh::lean_obj_tag(v___x_1384_) == 0 {
                        v_a_1385_ = crate::leanh::lean_ctor_get(v___x_1384_, 0);
                        v_isSharedCheck_1398_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1384_)) as u8;
                        if v_isSharedCheck_1398_ == 0 {
                            v___x_1387_ = v___x_1384_;
                            v_isShared_1388_ = v_isSharedCheck_1398_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1385_);
                            crate::leanh::lean_dec(v___x_1384_);
                            v___x_1387_ = crate::leanh::lean_box(0);
                            v_isShared_1388_ = v_isSharedCheck_1398_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_1382_);
                        crate::leanh::lean_del_object(v___x_1370_);
                        crate::leanh::lean_dec(v_discr_1367_);
                        crate::leanh::lean_dec_ref(v_resultType_1366_);
                        crate::leanh::lean_dec(v_typeName_1365_);
                        v_a_1399_ = crate::leanh::lean_ctor_get(v___x_1384_, 0);
                        v_isSharedCheck_1406_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1384_)) as u8;
                        if v_isSharedCheck_1406_ == 0 {
                            v___x_1401_ = v___x_1384_;
                            v_isShared_1402_ = v_isSharedCheck_1406_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1399_);
                            crate::leanh::lean_dec(v___x_1384_);
                            v___x_1401_ = crate::leanh::lean_box(0);
                            v_isShared_1402_ = v_isSharedCheck_1406_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1370_);
                    crate::leanh::lean_dec(v_discr_1367_);
                    crate::leanh::lean_dec_ref(v_resultType_1366_);
                    crate::leanh::lean_dec(v_typeName_1365_);
                    v_a_1407_ = crate::leanh::lean_ctor_get(v___x_1380_, 0);
                    v_isSharedCheck_1414_ = (!crate::leanh::lean_is_exclusive(v___x_1380_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v___x_1409_ = v___x_1380_;
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1407_);
                        crate::leanh::lean_dec(v___x_1380_);
                        v___x_1409_ = crate::leanh::lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1389_ = 1;
                if v_isShared_1371_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1370_, 3, v_a_1385_);
                    v___x_1391_ = v___x_1370_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_typeName_1365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_resultType_1366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_discr_1367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_a_1385_);
                    v___x_1391_ = v_reuseFailAlloc_1397_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1392_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
                v___x_1393_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1389_, v_fst_1382_, v___x_1392_);
                crate::leanh::lean_dec(v_fst_1382_);
                if v_isShared_1388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1387_, 0, v___x_1393_);
                    v___x_1395_ = v___x_1387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
                    v___x_1395_ = v_reuseFailAlloc_1396_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1395_;
            }
            5 => {
                if v_isShared_1402_ == 0 {
                    v___x_1404_ = v___x_1401_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1404_;
            }
            7 => {
                if v_isShared_1410_ == 0 {
                    v___x_1412_ = v___x_1409_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
                    v___x_1412_ = v_reuseFailAlloc_1413_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(
    mut v_c_1416_: *mut crate::leanh::LeanObject,
    mut v_decls_1417_: *mut crate::leanh::LeanObject,
    mut v_a_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_cases_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1488_: u8 = 0;
    let mut v_persistent_1489_: u8 = 0;
    let mut v_k_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1496_: u8 = 0;
    let mut v_persistent_1497_: u8 = 0;
    let mut v_objs_x3f_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_c_1416_) {
                    0 => {
                        v_decl_1423_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc_ref(v_decl_1423_);
                        v_k_1424_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc_ref(v_k_1424_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 2);
                        v___x_1425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1425_, 0, v_decl_1423_);
                        v___x_1426_ = lean_array_push(v_decls_1417_, v___x_1425_);
                        v_c_1416_ = v_k_1424_;
                        v_decls_1417_ = v___x_1426_;
                        state = 0;
                        continue;
                    }
                    2 => {
                        v_decl_1428_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc_ref(v_decl_1428_);
                        v_k_1429_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc_ref(v_k_1429_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 2);
                        v_params_1430_ = crate::leanh::lean_ctor_get(v_decl_1428_, 2);
                        crate::leanh::lean_inc_ref(v_params_1430_);
                        v_type_1431_ = crate::leanh::lean_ctor_get(v_decl_1428_, 3);
                        crate::leanh::lean_inc_ref(v_type_1431_);
                        v_value_1432_ = crate::leanh::lean_ctor_get(v_decl_1428_, 4);
                        crate::leanh::lean_inc_ref(v_value_1432_);
                        v___x_1433_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_value_1432_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
                        if crate::leanh::lean_obj_tag(v___x_1433_) == 0 {
                            v_a_1434_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                            v_isSharedCheck_1454_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1433_)) as u8;
                            if v_isSharedCheck_1454_ == 0 {
                                v___x_1436_ = v___x_1433_;
                                v_isShared_1437_ = v_isSharedCheck_1454_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1434_);
                                crate::leanh::lean_dec(v___x_1433_);
                                v___x_1436_ = crate::leanh::lean_box(0);
                                v_isShared_1437_ = v_isSharedCheck_1454_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_type_1431_);
                            crate::leanh::lean_dec_ref(v_params_1430_);
                            crate::leanh::lean_dec_ref(v_k_1429_);
                            crate::leanh::lean_dec_ref(v_decl_1428_);
                            crate::leanh::lean_dec_ref(v_decls_1417_);
                            return v___x_1433_;
                        }
                    }
                    4 => {
                        v_cases_1455_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc_ref(v_cases_1455_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 1);
                        v___x_1456_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_cases_1455_, v_decls_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
                        return v___x_1456_;
                    }
                    7 => {
                        v_fvarId_1457_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc(v_fvarId_1457_);
                        v_i_1458_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc(v_i_1458_);
                        v_y_1459_ = crate::leanh::lean_ctor_get(v_c_1416_, 2);
                        crate::leanh::lean_inc(v_y_1459_);
                        v_k_1460_ = crate::leanh::lean_ctor_get(v_c_1416_, 3);
                        crate::leanh::lean_inc_ref(v_k_1460_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 4);
                        v___x_1461_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1461_, 0, v_fvarId_1457_);
                        crate::leanh::lean_ctor_set(v___x_1461_, 1, v_i_1458_);
                        crate::leanh::lean_ctor_set(v___x_1461_, 2, v_y_1459_);
                        v___x_1462_ = lean_array_push(v_decls_1417_, v___x_1461_);
                        v_c_1416_ = v_k_1460_;
                        v_decls_1417_ = v___x_1462_;
                        state = 0;
                        continue;
                    }
                    8 => {
                        v_fvarId_1464_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc(v_fvarId_1464_);
                        v_i_1465_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc(v_i_1465_);
                        v_y_1466_ = crate::leanh::lean_ctor_get(v_c_1416_, 2);
                        crate::leanh::lean_inc(v_y_1466_);
                        v_k_1467_ = crate::leanh::lean_ctor_get(v_c_1416_, 3);
                        crate::leanh::lean_inc_ref(v_k_1467_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 4);
                        v___x_1468_ = crate::leanh::lean_alloc_ctor(4, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1468_, 0, v_fvarId_1464_);
                        crate::leanh::lean_ctor_set(v___x_1468_, 1, v_i_1465_);
                        crate::leanh::lean_ctor_set(v___x_1468_, 2, v_y_1466_);
                        v___x_1469_ = lean_array_push(v_decls_1417_, v___x_1468_);
                        v_c_1416_ = v_k_1467_;
                        v_decls_1417_ = v___x_1469_;
                        state = 0;
                        continue;
                    }
                    9 => {
                        v_fvarId_1471_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc(v_fvarId_1471_);
                        v_i_1472_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc(v_i_1472_);
                        v_offset_1473_ = crate::leanh::lean_ctor_get(v_c_1416_, 2);
                        crate::leanh::lean_inc(v_offset_1473_);
                        v_y_1474_ = crate::leanh::lean_ctor_get(v_c_1416_, 3);
                        crate::leanh::lean_inc(v_y_1474_);
                        v_ty_1475_ = crate::leanh::lean_ctor_get(v_c_1416_, 4);
                        crate::leanh::lean_inc_ref(v_ty_1475_);
                        v_k_1476_ = crate::leanh::lean_ctor_get(v_c_1416_, 5);
                        crate::leanh::lean_inc_ref(v_k_1476_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 6);
                        v___x_1477_ = crate::leanh::lean_alloc_ctor(5, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1477_, 0, v_fvarId_1471_);
                        crate::leanh::lean_ctor_set(v___x_1477_, 1, v_i_1472_);
                        crate::leanh::lean_ctor_set(v___x_1477_, 2, v_offset_1473_);
                        crate::leanh::lean_ctor_set(v___x_1477_, 3, v_y_1474_);
                        crate::leanh::lean_ctor_set(v___x_1477_, 4, v_ty_1475_);
                        v___x_1478_ = lean_array_push(v_decls_1417_, v___x_1477_);
                        v_c_1416_ = v_k_1476_;
                        v_decls_1417_ = v___x_1478_;
                        state = 0;
                        continue;
                    }
                    10 => {
                        v_fvarId_1480_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc(v_fvarId_1480_);
                        v_cidx_1481_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc(v_cidx_1481_);
                        v_k_1482_ = crate::leanh::lean_ctor_get(v_c_1416_, 2);
                        crate::leanh::lean_inc_ref(v_k_1482_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 3);
                        v___x_1483_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1483_, 0, v_fvarId_1480_);
                        crate::leanh::lean_ctor_set(v___x_1483_, 1, v_cidx_1481_);
                        v___x_1484_ = lean_array_push(v_decls_1417_, v___x_1483_);
                        v_c_1416_ = v_k_1482_;
                        v_decls_1417_ = v___x_1484_;
                        state = 0;
                        continue;
                    }
                    11 => {
                        v_fvarId_1486_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc(v_fvarId_1486_);
                        v_n_1487_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc(v_n_1487_);
                        v_check_1488_ = crate::leanh::lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_1489_ = crate::leanh::lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_1490_ = crate::leanh::lean_ctor_get(v_c_1416_, 2);
                        crate::leanh::lean_inc_ref(v_k_1490_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 3);
                        v___x_1491_ = crate::leanh::lean_alloc_ctor(7, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_1491_, 0, v_fvarId_1486_);
                        crate::leanh::lean_ctor_set(v___x_1491_, 1, v_n_1487_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1491_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v_check_1488_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1491_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v_persistent_1489_,
                        );
                        v___x_1492_ = lean_array_push(v_decls_1417_, v___x_1491_);
                        v_c_1416_ = v_k_1490_;
                        v_decls_1417_ = v___x_1492_;
                        state = 0;
                        continue;
                    }
                    12 => {
                        v_fvarId_1494_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc(v_fvarId_1494_);
                        v_n_1495_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc(v_n_1495_);
                        v_check_1496_ = crate::leanh::lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v_persistent_1497_ = crate::leanh::lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_1498_ = crate::leanh::lean_ctor_get(v_c_1416_, 2);
                        crate::leanh::lean_inc(v_objs_x3f_1498_);
                        v_k_1499_ = crate::leanh::lean_ctor_get(v_c_1416_, 3);
                        crate::leanh::lean_inc_ref(v_k_1499_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 4);
                        v___x_1500_ = crate::leanh::lean_alloc_ctor(8, 3, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_1500_, 0, v_fvarId_1494_);
                        crate::leanh::lean_ctor_set(v___x_1500_, 1, v_n_1495_);
                        crate::leanh::lean_ctor_set(v___x_1500_, 2, v_objs_x3f_1498_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1500_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v_check_1496_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1500_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                            v_persistent_1497_,
                        );
                        v___x_1501_ = lean_array_push(v_decls_1417_, v___x_1500_);
                        v_c_1416_ = v_k_1499_;
                        v_decls_1417_ = v___x_1501_;
                        state = 0;
                        continue;
                    }
                    13 => {
                        v_fvarId_1503_ = crate::leanh::lean_ctor_get(v_c_1416_, 0);
                        crate::leanh::lean_inc(v_fvarId_1503_);
                        v_k_1504_ = crate::leanh::lean_ctor_get(v_c_1416_, 1);
                        crate::leanh::lean_inc_ref(v_k_1504_);
                        crate::leanh::lean_dec_ref_known(v_c_1416_, 2);
                        v___x_1505_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1505_, 0, v_fvarId_1503_);
                        v___x_1506_ = lean_array_push(v_decls_1417_, v___x_1505_);
                        v_c_1416_ = v_k_1504_;
                        v_decls_1417_ = v___x_1506_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        v___x_1508_ = 1;
                        v___x_1509_ = l_Lean_Compiler_LCNF_attachCodeDecls(
                            v___x_1508_,
                            v_decls_1417_,
                            v_c_1416_,
                        );
                        crate::leanh::lean_dec_ref(v_decls_1417_);
                        v___x_1510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1509_);
                        return v___x_1510_;
                    }
                }
            }
            1 => {
                v___x_1438_ = 1;
                v___x_1439_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1438_, v_decl_1428_, v_type_1431_, v_params_1430_, v_a_1434_, v_a_1419_);
                if crate::leanh::lean_obj_tag(v___x_1439_) == 0 {
                    v_a_1440_ = crate::leanh::lean_ctor_get(v___x_1439_, 0);
                    crate::leanh::lean_inc(v_a_1440_);
                    crate::leanh::lean_dec_ref_known(v___x_1439_, 1);
                    if v_isShared_1437_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1436_, 2);
                        crate::leanh::lean_ctor_set(v___x_1436_, 0, v_a_1440_);
                        v___x_1442_ = v___x_1436_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1440_);
                        v___x_1442_ = v_reuseFailAlloc_1445_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1436_);
                    crate::leanh::lean_dec_ref(v_k_1429_);
                    crate::leanh::lean_dec_ref(v_decls_1417_);
                    v_a_1446_ = crate::leanh::lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1453_ = (!crate::leanh::lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1448_ = v___x_1439_;
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1446_);
                        crate::leanh::lean_dec(v___x_1439_);
                        v___x_1448_ = crate::leanh::lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1443_ = lean_array_push(v_decls_1417_, v___x_1442_);
                v_c_1416_ = v_k_1429_;
                v_decls_1417_ = v___x_1443_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1449_ == 0 {
                    v___x_1451_ = v___x_1448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(
    mut v_code_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
    mut v_a_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ =
        l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0;
    v___x_1518_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(
        v_code_1511_,
        v___x_1517_,
        v_a_1512_,
        v_a_1513_,
        v_a_1514_,
        v_a_1515_,
    );
    return v___x_1518_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___boxed(
    mut v_i_1519_: *mut crate::leanh::LeanObject,
    mut v_as_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v_i_1519_, v_as_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
    crate::leanh::lean_dec(v___y_1524_);
    crate::leanh::lean_dec_ref(v___y_1523_);
    crate::leanh::lean_dec(v___y_1522_);
    crate::leanh::lean_dec_ref(v___y_1521_);
    return v_res_1526_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___boxed(
    mut v_c_1527_: *mut crate::leanh::LeanObject,
    mut v_decls_1528_: *mut crate::leanh::LeanObject,
    mut v_a_1529_: *mut crate::leanh::LeanObject,
    mut v_a_1530_: *mut crate::leanh::LeanObject,
    mut v_a_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(
        v_c_1527_,
        v_decls_1528_,
        v_a_1529_,
        v_a_1530_,
        v_a_1531_,
        v_a_1532_,
    );
    crate::leanh::lean_dec(v_a_1532_);
    crate::leanh::lean_dec_ref(v_a_1531_);
    crate::leanh::lean_dec(v_a_1530_);
    crate::leanh::lean_dec_ref(v_a_1529_);
    return v_res_1534_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go___boxed(
    mut v_c_1535_: *mut crate::leanh::LeanObject,
    mut v_decls_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
    mut v_a_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(
        v_c_1535_,
        v_decls_1536_,
        v_a_1537_,
        v_a_1538_,
        v_a_1539_,
        v_a_1540_,
    );
    crate::leanh::lean_dec(v_a_1540_);
    crate::leanh::lean_dec_ref(v_a_1539_);
    crate::leanh::lean_dec(v_a_1538_);
    crate::leanh::lean_dec_ref(v_a_1537_);
    return v_res_1542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(
    mut v_00_u03b2_1543_: *mut crate::leanh::LeanObject,
    mut v_m_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_b_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v_m_1544_, v_a_1545_, v_b_1546_);
    return v___x_1547_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3(
    mut v_00_u03b2_1548_: *mut crate::leanh::LeanObject,
    mut v_data_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_data_1549_);
    return v___x_1550_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1551_: *mut crate::leanh::LeanObject,
    mut v_i_1552_: *mut crate::leanh::LeanObject,
    mut v_source_1553_: *mut crate::leanh::LeanObject,
    mut v_target_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v_i_1552_, v_source_1553_, v_target_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1556_: *mut crate::leanh::LeanObject,
    mut v_x_1557_: *mut crate::leanh::LeanObject,
    mut v_x_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1557_, v_x_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(
    mut v_f_1560_: *mut crate::leanh::LeanObject,
    mut v_v_1561_: *mut crate::leanh::LeanObject,
    mut v___y_1562_: *mut crate::leanh::LeanObject,
    mut v___y_1563_: *mut crate::leanh::LeanObject,
    mut v___y_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_a_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_1561_) == 0 {
                    v_code_1567_ = crate::leanh::lean_ctor_get(v_v_1561_, 0);
                    v_isSharedCheck_1591_ = (!crate::leanh::lean_is_exclusive(v_v_1561_)) as u8;
                    if v_isSharedCheck_1591_ == 0 {
                        v___x_1569_ = v_v_1561_;
                        v_isShared_1570_ = v_isSharedCheck_1591_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_1567_);
                        crate::leanh::lean_dec(v_v_1561_);
                        v___x_1569_ = crate::leanh::lean_box(0);
                        v_isShared_1570_ = v_isSharedCheck_1591_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_1560_);
                    v___x_1592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1592_, 0, v_v_1561_);
                    return v___x_1592_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1565_);
                crate::leanh::lean_inc_ref(v___y_1564_);
                crate::leanh::lean_inc(v___y_1563_);
                crate::leanh::lean_inc_ref(v___y_1562_);
                v___x_1571_ = crate::leanh::lean_apply_6(
                    v_f_1560_,
                    v_code_1567_,
                    v___y_1562_,
                    v___y_1563_,
                    v___y_1564_,
                    v___y_1565_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1571_) == 0 {
                    v_a_1572_ = crate::leanh::lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1582_ = (!crate::leanh::lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1582_ == 0 {
                        v___x_1574_ = v___x_1571_;
                        v_isShared_1575_ = v_isSharedCheck_1582_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1572_);
                        crate::leanh::lean_dec(v___x_1571_);
                        v___x_1574_ = crate::leanh::lean_box(0);
                        v_isShared_1575_ = v_isSharedCheck_1582_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1569_);
                    v_a_1583_ = crate::leanh::lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1590_ = (!crate::leanh::lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1590_ == 0 {
                        v___x_1585_ = v___x_1571_;
                        v_isShared_1586_ = v_isSharedCheck_1590_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1583_);
                        crate::leanh::lean_dec(v___x_1571_);
                        v___x_1585_ = crate::leanh::lean_box(0);
                        v_isShared_1586_ = v_isSharedCheck_1590_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1569_, 0, v_a_1572_);
                    v___x_1577_ = v___x_1569_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1572_);
                    v___x_1577_ = v_reuseFailAlloc_1581_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1574_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1574_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1579_;
            }
            5 => {
                if v_isShared_1586_ == 0 {
                    v___x_1588_ = v___x_1585_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg___boxed(
    mut v_f_1593_: *mut crate::leanh::LeanObject,
    mut v_v_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_1593_, v_v_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
    crate::leanh::lean_dec(v___y_1598_);
    crate::leanh::lean_dec_ref(v___y_1597_);
    crate::leanh::lean_dec(v___y_1596_);
    crate::leanh::lean_dec_ref(v___y_1595_);
    return v_res_1600_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(
    mut v_pu_1601_: u8,
    mut v_f_1602_: *mut crate::leanh::LeanObject,
    mut v_v_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
    mut v___y_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_1602_, v_v_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___boxed(
    mut v_pu_1610_: *mut crate::leanh::LeanObject,
    mut v_f_1611_: *mut crate::leanh::LeanObject,
    mut v_v_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1618_: u8 = 0;
    let mut v_res_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1618_ = (crate::leanh::lean_unbox(v_pu_1610_) as u8);
    v_res_1619_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(v_pu_boxed_1618_, v_f_1611_, v_v_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
    crate::leanh::lean_dec(v___y_1616_);
    crate::leanh::lean_dec_ref(v___y_1615_);
    crate::leanh::lean_dec(v___y_1614_);
    crate::leanh::lean_dec_ref(v___y_1613_);
    return v_res_1619_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = crate::leanh::lean_box(0);
    v___x_1622_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1623_ = lean_mk_array(v___x_1622_, v___x_1621_);
    return v___x_1623_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once), _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1);
    v___x_1625_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1626_, 0, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1626_, 1, v___x_1624_);
    return v___x_1626_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(
    mut v_decl_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_1635_: u8 = 0;
    let mut v_inlineAttr_x3f_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___f_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1653_: u8 = 0;
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1657_: u8 = 0;
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_1633_ = crate::leanh::lean_ctor_get(v_decl_1627_, 0);
                v_value_1634_ = crate::leanh::lean_ctor_get(v_decl_1627_, 1);
                v_recursive_1635_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_1627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_1636_ = crate::leanh::lean_ctor_get(v_decl_1627_, 2);
                v_isSharedCheck_1658_ = (!crate::leanh::lean_is_exclusive(v_decl_1627_)) as u8;
                if v_isSharedCheck_1658_ == 0 {
                    v___x_1638_ = v_decl_1627_;
                    v_isShared_1639_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_1636_);
                    crate::leanh::lean_inc(v_value_1634_);
                    crate::leanh::lean_inc(v_toSignature_1633_);
                    crate::leanh::lean_dec(v_decl_1627_);
                    v___x_1638_ = crate::leanh::lean_box(0);
                    v_isShared_1639_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1640_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0;
                v___x_1641_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v___f_1640_, v_value_1634_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
                if crate::leanh::lean_obj_tag(v___x_1641_) == 0 {
                    v_a_1642_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                    crate::leanh::lean_inc(v_a_1642_);
                    crate::leanh::lean_dec_ref_known(v___x_1641_, 1);
                    v___x_1643_ = 1;
                    if v_isShared_1639_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1638_, 1, v_a_1642_);
                        v___x_1645_ = v___x_1638_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_toSignature_1633_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_a_1642_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1649_,
                            2,
                            v_inlineAttr_x3f_1636_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1649_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v_recursive_1635_,
                        );
                        v___x_1645_ = v_reuseFailAlloc_1649_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1638_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_1636_);
                    crate::leanh::lean_dec_ref(v_toSignature_1633_);
                    v_a_1650_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1657_ = (!crate::leanh::lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1657_ == 0 {
                        v___x_1652_ = v___x_1641_;
                        v_isShared_1653_ = v_isSharedCheck_1657_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1650_);
                        crate::leanh::lean_dec(v___x_1641_);
                        v___x_1652_ = crate::leanh::lean_box(0);
                        v_isShared_1653_ = v_isSharedCheck_1657_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1646_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once), _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2);
                v___x_1647_ = 0;
                v___x_1648_ = l_Lean_Compiler_LCNF_Decl_internalize(
                    v___x_1643_,
                    v___x_1645_,
                    v___x_1646_,
                    v___x_1647_,
                    v_a_1628_,
                    v_a_1629_,
                    v_a_1630_,
                    v_a_1631_,
                );
                return v___x_1648_;
            }
            3 => {
                if v_isShared_1653_ == 0 {
                    v___x_1655_ = v___x_1652_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
                    v___x_1655_ = v_reuseFailAlloc_1656_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed(
    mut v_decl_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
    mut v_a_1661_: *mut crate::leanh::LeanObject,
    mut v_a_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
    mut v_a_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(
        v_decl_1659_,
        v_a_1660_,
        v_a_1661_,
        v_a_1662_,
        v_a_1663_,
    );
    crate::leanh::lean_dec(v_a_1663_);
    crate::leanh::lean_dec_ref(v_a_1662_);
    crate::leanh::lean_dec(v_a_1661_);
    crate::leanh::lean_dec_ref(v_a_1660_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_Compiler_LCNF_pushProj(
    mut v_occurrence_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_Compiler_LCNF_pushProj___closed__1;
    v___x_1672_ = 2;
    v___x_1673_ = l_Lean_Compiler_LCNF_pushProj___closed__2;
    v___x_1674_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_1671_,
        v___x_1672_,
        v___x_1673_,
        v_occurrence_1670_,
    );
    return v___x_1674_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_;
    v___x_1746_ = 1;
    v___x_1747_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_;
    v___x_1748_ = l_Lean_registerTraceClass(v___x_1745_, v___x_1746_, v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2____boxed(
    mut v_a_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
    return v_res_1750_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PushProj(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PushProj(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_PushProj(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PushProj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PushProj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PushProj(builtin);
}
