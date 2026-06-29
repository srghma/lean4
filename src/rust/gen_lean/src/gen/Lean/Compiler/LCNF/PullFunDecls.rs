// Lean compiler output
// Module: Lean.Compiler.LCNF.PullFunDecls
// Imports: Lean.Compiler.LCNF.DependsOn Lean.Compiler.LCNF.PassManager
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_fset, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_nat_add, lean_nat_dec_lt, lean_ptr_addr,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg, l_Lean_Compiler_LCNF_FunDecl_collectUsed,
    l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg;
use crate::r#gen::Lean::Compiler::LCNF::DependsOn::{
    initialize_Lean_Compiler_LCNF_DependsOn, runtime_initialize_Lean_Compiler_LCNF_DependsOn,
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
static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [112, 117, 108, 108, 70, 117, 110, 68, 101, 99, 108, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullFunDecls___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15479406399762191914 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullFunDecls___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_Decl_pullFunDecls___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_pullFunDecls: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value) as *mut crate::leanh::LeanObject,7687188514397653396 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 117, 108, 108, 70, 117, 110, 68, 101, 99, 108, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4715093308645774882 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,8361423566811915395 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9903248596004213070 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,424871438967119852 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10437388805546877613 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,491910158757896708 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8630099969334220429 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,668284432093445752 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16269612643220945362 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6062304044350350739 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12890017594083057032 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1553090079 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,11458291349318782630 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5573388920595387873 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11256589942589999705 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,8502987044875405700 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = 0;
    v___x_1173_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(v___x_1172_);
    return v___x_1173_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_instInhabitedFVarIdHashSet;
    v___x_1175_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0,
    );
    v___x_1176_ = 0;
    v___x_1177_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1177_, 0, v___x_1175_);
    crate::leanh::lean_ctor_set(v___x_1177_, 1, v___x_1174_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1177_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_1176_,
    );
    return v___x_1177_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1,
    );
    return v___x_1178_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
    return v___x_1179_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(
    mut v_a_1180_: *mut crate::leanh::LeanObject,
    mut v_x_1181_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1182_: u8 = 0;
    let mut v_key_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1181_) == 0 {
                    v___x_1182_ = 0;
                    return v___x_1182_;
                } else {
                    v_key_1183_ = crate::leanh::lean_ctor_get(v_x_1181_, 0);
                    v_tail_1184_ = crate::leanh::lean_ctor_get(v_x_1181_, 2);
                    v___x_1185_ = l_Lean_instBEqFVarId_beq(v_key_1183_, v_a_1180_);
                    if v___x_1185_ == 0 {
                        v_x_1181_ = v_tail_1184_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1185_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg___boxed(
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_x_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1189_: u8 = 0;
    let mut v_r_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_1187_, v_x_1188_);
    crate::leanh::lean_dec(v_x_1188_);
    crate::leanh::lean_dec(v_a_1187_);
    v_r_1190_ = crate::leanh::lean_box((v_res_1189_) as usize);
    return v_r_1190_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(
    mut v_m_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u64 = 0;
    let mut v___x_1196_: u64 = 0;
    let mut v___x_1197_: u64 = 0;
    let mut v_fold_1198_: u64 = 0;
    let mut v___x_1199_: u64 = 0;
    let mut v___x_1200_: u64 = 0;
    let mut v___x_1201_: u64 = 0;
    let mut v___x_1202_: usize = 0;
    let mut v___x_1203_: usize = 0;
    let mut v___x_1204_: usize = 0;
    let mut v___x_1205_: usize = 0;
    let mut v___x_1206_: usize = 0;
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: u8 = 0;
    v_buckets_1193_ = crate::leanh::lean_ctor_get(v_m_1191_, 1);
    v___x_1194_ = lean_array_get_size(v_buckets_1193_);
    v___x_1195_ = l_Lean_instHashableFVarId_hash(v_a_1192_);
    v___x_1196_ = 32u64;
    v___x_1197_ = lean_uint64_shift_right(v___x_1195_, v___x_1196_);
    v_fold_1198_ = lean_uint64_xor(v___x_1195_, v___x_1197_);
    v___x_1199_ = 16u64;
    v___x_1200_ = lean_uint64_shift_right(v_fold_1198_, v___x_1199_);
    v___x_1201_ = lean_uint64_xor(v_fold_1198_, v___x_1200_);
    v___x_1202_ = lean_uint64_to_usize(v___x_1201_);
    v___x_1203_ = lean_usize_of_nat(v___x_1194_);
    v___x_1204_ = 1usize;
    v___x_1205_ = lean_usize_sub(v___x_1203_, v___x_1204_);
    v___x_1206_ = lean_usize_land(v___x_1202_, v___x_1205_);
    v___x_1207_ = lean_array_uget_borrowed(v_buckets_1193_, v___x_1206_);
    v___x_1208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_1192_, v___x_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg___boxed(
    mut v_m_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1211_: u8 = 0;
    let mut v_r_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_1209_, v_a_1210_);
    crate::leanh::lean_dec(v_a_1210_);
    crate::leanh::lean_dec_ref(v_m_1209_);
    v_r_1212_ = crate::leanh::lean_box((v_res_1211_) as usize);
    return v_r_1212_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(
    mut v_fvarId_1213_: *mut crate::leanh::LeanObject,
    mut v_as_1214_: *mut crate::leanh::LeanObject,
    mut v_keep_1215_: *mut crate::leanh::LeanObject,
    mut v_dep_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v_used_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_1214_) == 0 {
                    v___x_1218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1218_, 0, v_keep_1215_);
                    crate::leanh::lean_ctor_set(v___x_1218_, 1, v_dep_1216_);
                    v___x_1219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1219_, 0, v___x_1218_);
                    return v___x_1219_;
                } else {
                    v_head_1220_ = crate::leanh::lean_ctor_get(v_as_1214_, 0);
                    v_tail_1221_ = crate::leanh::lean_ctor_get(v_as_1214_, 1);
                    v_isSharedCheck_1235_ = (!crate::leanh::lean_is_exclusive(v_as_1214_)) as u8;
                    if v_isSharedCheck_1235_ == 0 {
                        v___x_1223_ = v_as_1214_;
                        v_isShared_1224_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1221_);
                        crate::leanh::lean_inc(v_head_1220_);
                        crate::leanh::lean_dec(v_as_1214_);
                        v___x_1223_ = crate::leanh::lean_box(0);
                        v_isShared_1224_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_used_1225_ = crate::leanh::lean_ctor_get(v_head_1220_, 1);
                v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_1225_, v_fvarId_1213_);
                if v___x_1226_ == 0 {
                    if v_isShared_1224_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1223_, 1, v_keep_1215_);
                        v___x_1228_ = v___x_1223_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1230_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_head_1220_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_keep_1215_);
                        v___x_1228_ = v_reuseFailAlloc_1230_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1224_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1223_, 1, v_dep_1216_);
                        v___x_1232_ = v___x_1223_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1234_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_head_1220_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_dep_1216_);
                        v___x_1232_ = v_reuseFailAlloc_1234_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_as_1214_ = v_tail_1221_;
                v_keep_1215_ = v___x_1228_;
                state = 0;
                continue;
            }
            3 => {
                v_as_1214_ = v_tail_1221_;
                v_dep_1216_ = v___x_1232_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg___boxed(
    mut v_fvarId_1236_: *mut crate::leanh::LeanObject,
    mut v_as_1237_: *mut crate::leanh::LeanObject,
    mut v_keep_1238_: *mut crate::leanh::LeanObject,
    mut v_dep_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1241_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_1236_, v_as_1237_, v_keep_1238_, v_dep_1239_);
    crate::leanh::lean_dec(v_fvarId_1236_);
    return v_res_1241_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(
    mut v_fvarId_1242_: *mut crate::leanh::LeanObject,
    mut v_as_1243_: *mut crate::leanh::LeanObject,
    mut v_keep_1244_: *mut crate::leanh::LeanObject,
    mut v_dep_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_1242_, v_as_1243_, v_keep_1244_, v_dep_1245_);
    return v___x_1249_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___boxed(
    mut v_fvarId_1250_: *mut crate::leanh::LeanObject,
    mut v_as_1251_: *mut crate::leanh::LeanObject,
    mut v_keep_1252_: *mut crate::leanh::LeanObject,
    mut v_dep_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1257_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(v_fvarId_1250_, v_as_1251_, v_keep_1252_, v_dep_1253_, v_a_1254_, v_a_1255_);
    crate::leanh::lean_dec(v_a_1255_);
    crate::leanh::lean_dec_ref(v_a_1254_);
    crate::leanh::lean_dec(v_fvarId_1250_);
    return v_res_1257_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(
    mut v_00_u03b2_1258_: *mut crate::leanh::LeanObject,
    mut v_m_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1261_: u8 = 0;
    v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_1259_, v_a_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___boxed(
    mut v_00_u03b2_1262_: *mut crate::leanh::LeanObject,
    mut v_m_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1265_: u8 = 0;
    let mut v_r_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(v_00_u03b2_1262_, v_m_1263_, v_a_1264_);
    crate::leanh::lean_dec(v_a_1264_);
    crate::leanh::lean_dec_ref(v_m_1263_);
    v_r_1266_ = crate::leanh::lean_box((v_res_1265_) as usize);
    return v_r_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(
    mut v_00_u03b2_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_x_1269_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1270_: u8 = 0;
    v___x_1270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_1268_, v_x_1269_);
    return v___x_1270_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_x_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1274_: u8 = 0;
    let mut v_r_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(v_00_u03b2_1271_, v_a_1272_, v_x_1273_);
    crate::leanh::lean_dec(v_x_1273_);
    crate::leanh::lean_dec(v_a_1272_);
    v_r_1275_ = crate::leanh::lean_box((v_res_1274_) as usize);
    return v_r_1275_;
}
pub unsafe fn l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(
    mut v_fvarId_1276_: *mut crate::leanh::LeanObject,
    mut v_x_1277_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1278_: u8 = 0;
    let mut v_head_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1277_) == 0 {
                    v___x_1278_ = 0;
                    return v___x_1278_;
                } else {
                    v_head_1279_ = crate::leanh::lean_ctor_get(v_x_1277_, 0);
                    v_tail_1280_ = crate::leanh::lean_ctor_get(v_x_1277_, 1);
                    v_used_1281_ = crate::leanh::lean_ctor_get(v_head_1279_, 1);
                    v___x_1282_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_1281_, v_fvarId_1276_);
                    if v___x_1282_ == 0 {
                        v_x_1277_ = v_tail_1280_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1282_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0___boxed(
    mut v_fvarId_1284_: *mut crate::leanh::LeanObject,
    mut v_x_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1286_: u8 = 0;
    let mut v_r_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1286_ = l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(
        v_fvarId_1284_,
        v_x_1285_,
    );
    crate::leanh::lean_dec(v_x_1285_);
    crate::leanh::lean_dec(v_fvarId_1284_);
    v_r_1287_ = crate::leanh::lean_box((v_res_1286_) as usize);
    return v_r_1287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(
    mut v_fvarId_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v_fst_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1291_ = lean_st_ref_get(v_a_1289_);
                v___x_1292_ =
                    l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(
                        v_fvarId_1288_,
                        v___x_1291_,
                    );
                if v___x_1292_ == 0 {
                    crate::leanh::lean_dec(v___x_1291_);
                    v___x_1293_ = crate::leanh::lean_box(0);
                    v___x_1294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1294_, 0, v___x_1293_);
                    return v___x_1294_;
                } else {
                    v___x_1295_ = crate::leanh::lean_box(0);
                    v___x_1296_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_1288_, v___x_1291_, v___x_1295_, v___x_1295_);
                    v_a_1297_ = crate::leanh::lean_ctor_get(v___x_1296_, 0);
                    v_isSharedCheck_1307_ = (!crate::leanh::lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1299_ = v___x_1296_;
                        v_isShared_1300_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1297_);
                        crate::leanh::lean_dec(v___x_1296_);
                        v___x_1299_ = crate::leanh::lean_box(0);
                        v_isShared_1300_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1301_ = crate::leanh::lean_ctor_get(v_a_1297_, 0);
                crate::leanh::lean_inc(v_fst_1301_);
                v_snd_1302_ = crate::leanh::lean_ctor_get(v_a_1297_, 1);
                crate::leanh::lean_inc(v_snd_1302_);
                crate::leanh::lean_dec(v_a_1297_);
                v___x_1303_ = lean_st_ref_set(v_a_1289_, v_fst_1301_);
                if v_isShared_1300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1299_, 0, v_snd_1302_);
                    v___x_1305_ = v___x_1299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_snd_1302_);
                    v___x_1305_ = v_reuseFailAlloc_1306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg___boxed(
    mut v_fvarId_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_1308_, v_a_1309_);
    crate::leanh::lean_dec(v_a_1309_);
    crate::leanh::lean_dec(v_fvarId_1308_);
    return v_res_1311_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(
    mut v_fvarId_1312_: *mut crate::leanh::LeanObject,
    mut v_a_1313_: *mut crate::leanh::LeanObject,
    mut v_a_1314_: *mut crate::leanh::LeanObject,
    mut v_a_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_1312_, v_a_1313_);
    return v___x_1319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___boxed(
    mut v_fvarId_1320_: *mut crate::leanh::LeanObject,
    mut v_a_1321_: *mut crate::leanh::LeanObject,
    mut v_a_1322_: *mut crate::leanh::LeanObject,
    mut v_a_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(
        v_fvarId_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
        v_a_1324_,
        v_a_1325_,
    );
    crate::leanh::lean_dec(v_a_1325_);
    crate::leanh::lean_dec_ref(v_a_1324_);
    crate::leanh::lean_dec(v_a_1323_);
    crate::leanh::lean_dec_ref(v_a_1322_);
    crate::leanh::lean_dec(v_a_1321_);
    crate::leanh::lean_dec(v_fvarId_1320_);
    return v_res_1327_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
    mut v_todo_1328_: *mut crate::leanh::LeanObject,
    mut v_acc_1329_: *mut crate::leanh::LeanObject,
    mut v_a_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_todo_1328_) == 0 {
                    v___x_1332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1332_, 0, v_acc_1329_);
                    return v___x_1332_;
                } else {
                    v_head_1333_ = crate::leanh::lean_ctor_get(v_todo_1328_, 0);
                    crate::leanh::lean_inc(v_head_1333_);
                    v_decl_1334_ = crate::leanh::lean_ctor_get(v_head_1333_, 0);
                    v_tail_1335_ = crate::leanh::lean_ctor_get(v_todo_1328_, 1);
                    crate::leanh::lean_inc(v_tail_1335_);
                    crate::leanh::lean_dec_ref_known(v_todo_1328_, 2);
                    v_fvarId_1336_ = crate::leanh::lean_ctor_get(v_decl_1334_, 0);
                    v___x_1337_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(
                        v_fvarId_1336_,
                        v_a_1330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1337_) == 0 {
                        v_a_1338_ = crate::leanh::lean_ctor_get(v___x_1337_, 0);
                        crate::leanh::lean_inc(v_a_1338_);
                        crate::leanh::lean_dec_ref_known(v___x_1337_, 1);
                        v___x_1339_ = l_List_appendTR___redArg(v_a_1338_, v_tail_1335_);
                        v___x_1340_ = lean_array_push(v_acc_1329_, v_head_1333_);
                        v_todo_1328_ = v___x_1339_;
                        v_acc_1329_ = v___x_1340_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1335_);
                        crate::leanh::lean_dec(v_head_1333_);
                        crate::leanh::lean_dec_ref(v_acc_1329_);
                        v_a_1342_ = crate::leanh::lean_ctor_get(v___x_1337_, 0);
                        v_isSharedCheck_1349_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1337_)) as u8;
                        if v_isSharedCheck_1349_ == 0 {
                            v___x_1344_ = v___x_1337_;
                            v_isShared_1345_ = v_isSharedCheck_1349_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1342_);
                            crate::leanh::lean_dec(v___x_1337_);
                            v___x_1344_ = crate::leanh::lean_box(0);
                            v_isShared_1345_ = v_isSharedCheck_1349_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1345_ == 0 {
                    v___x_1347_ = v___x_1344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
                    v___x_1347_ = v_reuseFailAlloc_1348_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg___boxed(
    mut v_todo_1350_: *mut crate::leanh::LeanObject,
    mut v_acc_1351_: *mut crate::leanh::LeanObject,
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
        v_todo_1350_,
        v_acc_1351_,
        v_a_1352_,
    );
    crate::leanh::lean_dec(v_a_1352_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(
    mut v_todo_1355_: *mut crate::leanh::LeanObject,
    mut v_acc_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
        v_todo_1355_,
        v_acc_1356_,
        v_a_1357_,
    );
    return v___x_1363_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___boxed(
    mut v_todo_1364_: *mut crate::leanh::LeanObject,
    mut v_acc_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
    mut v_a_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(
        v_todo_1364_,
        v_acc_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
        v_a_1370_,
    );
    crate::leanh::lean_dec(v_a_1370_);
    crate::leanh::lean_dec_ref(v_a_1369_);
    crate::leanh::lean_dec(v_a_1368_);
    crate::leanh::lean_dec_ref(v_a_1367_);
    crate::leanh::lean_dec(v_a_1366_);
    return v_res_1372_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(
    mut v_fvarId_1375_: *mut crate::leanh::LeanObject,
    mut v_a_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1378_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(
                    v_fvarId_1375_,
                    v_a_1376_,
                );
                if crate::leanh::lean_obj_tag(v___x_1378_) == 0 {
                    v_a_1379_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                    crate::leanh::lean_inc(v_a_1379_);
                    crate::leanh::lean_dec_ref_known(v___x_1378_, 1);
                    v___x_1380_ =
                        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0;
                    v___x_1381_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
                        v_a_1379_,
                        v___x_1380_,
                        v_a_1376_,
                    );
                    return v___x_1381_;
                } else {
                    v_a_1382_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                    v_isSharedCheck_1389_ = (!crate::leanh::lean_is_exclusive(v___x_1378_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1384_ = v___x_1378_;
                        v_isShared_1385_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1382_);
                        crate::leanh::lean_dec(v___x_1378_);
                        v___x_1384_ = crate::leanh::lean_box(0);
                        v_isShared_1385_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1385_ == 0 {
                    v___x_1387_ = v___x_1384_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
                    v___x_1387_ = v_reuseFailAlloc_1388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___boxed(
    mut v_fvarId_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_1390_, v_a_1391_);
    crate::leanh::lean_dec(v_a_1391_);
    crate::leanh::lean_dec(v_fvarId_1390_);
    return v_res_1393_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(
    mut v_fvarId_1394_: *mut crate::leanh::LeanObject,
    mut v_a_1395_: *mut crate::leanh::LeanObject,
    mut v_a_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_1394_, v_a_1395_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___boxed(
    mut v_fvarId_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1409_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(
        v_fvarId_1402_,
        v_a_1403_,
        v_a_1404_,
        v_a_1405_,
        v_a_1406_,
        v_a_1407_,
    );
    crate::leanh::lean_dec(v_a_1407_);
    crate::leanh::lean_dec_ref(v_a_1406_);
    crate::leanh::lean_dec(v_a_1405_);
    crate::leanh::lean_dec_ref(v_a_1404_);
    crate::leanh::lean_dec(v_a_1403_);
    crate::leanh::lean_dec(v_fvarId_1402_);
    return v_res_1409_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(
    mut v_as_1410_: *mut crate::leanh::LeanObject,
    mut v_sz_1411_: usize,
    mut v_i_1412_: usize,
    mut v_b_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: u8 = 0;
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: usize = 0;
    let mut v___x_1424_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1416_ = lean_usize_dec_lt(v_i_1412_, v_sz_1411_);
                if v___x_1416_ == 0 {
                    v___x_1417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1417_, 0, v_b_1413_);
                    return v___x_1417_;
                } else {
                    v_a_1418_ = lean_array_uget_borrowed(v_as_1410_, v_i_1412_);
                    v_fvarId_1419_ = crate::leanh::lean_ctor_get(v_a_1418_, 0);
                    v___x_1420_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(
                        v_fvarId_1419_,
                        v___y_1414_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1420_) == 0 {
                        v_a_1421_ = crate::leanh::lean_ctor_get(v___x_1420_, 0);
                        crate::leanh::lean_inc(v_a_1421_);
                        crate::leanh::lean_dec_ref_known(v___x_1420_, 1);
                        v___x_1422_ = l_Array_append___redArg(v_b_1413_, v_a_1421_);
                        crate::leanh::lean_dec(v_a_1421_);
                        v___x_1423_ = 1usize;
                        v___x_1424_ = lean_usize_add(v_i_1412_, v___x_1423_);
                        v_i_1412_ = v___x_1424_;
                        v_b_1413_ = v___x_1422_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1413_);
                        return v___x_1420_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg___boxed(
    mut v_as_1426_: *mut crate::leanh::LeanObject,
    mut v_sz_1427_: *mut crate::leanh::LeanObject,
    mut v_i_1428_: *mut crate::leanh::LeanObject,
    mut v_b_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1432_: usize = 0;
    let mut v_i_boxed_1433_: usize = 0;
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1432_ = crate::leanh::lean_unbox_usize(v_sz_1427_);
    crate::leanh::lean_dec(v_sz_1427_);
    v_i_boxed_1433_ = crate::leanh::lean_unbox_usize(v_i_1428_);
    crate::leanh::lean_dec(v_i_1428_);
    v_res_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_1426_, v_sz_boxed_1432_, v_i_boxed_1433_, v_b_1429_, v___y_1430_);
    crate::leanh::lean_dec(v___y_1430_);
    crate::leanh::lean_dec_ref(v_as_1426_);
    return v_res_1434_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(
    mut v_params_1435_: *mut crate::leanh::LeanObject,
    mut v_a_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_acc_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1443_: usize = 0;
    let mut v___x_1444_: usize = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_acc_1442_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0;
    v_sz_1443_ = lean_array_size(v_params_1435_);
    v___x_1444_ = 0usize;
    v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_params_1435_, v_sz_1443_, v___x_1444_, v_acc_1442_, v_a_1436_);
    return v___x_1445_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg___boxed(
    mut v_params_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
    mut v_a_1448_: *mut crate::leanh::LeanObject,
    mut v_a_1449_: *mut crate::leanh::LeanObject,
    mut v_a_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
    mut v_a_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(
        v_params_1446_,
        v_a_1447_,
        v_a_1448_,
        v_a_1449_,
        v_a_1450_,
        v_a_1451_,
    );
    crate::leanh::lean_dec(v_a_1451_);
    crate::leanh::lean_dec_ref(v_a_1450_);
    crate::leanh::lean_dec(v_a_1449_);
    crate::leanh::lean_dec_ref(v_a_1448_);
    crate::leanh::lean_dec(v_a_1447_);
    crate::leanh::lean_dec_ref(v_params_1446_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(
    mut v_pu_1454_: u8,
    mut v_params_1455_: *mut crate::leanh::LeanObject,
    mut v_a_1456_: *mut crate::leanh::LeanObject,
    mut v_a_1457_: *mut crate::leanh::LeanObject,
    mut v_a_1458_: *mut crate::leanh::LeanObject,
    mut v_a_1459_: *mut crate::leanh::LeanObject,
    mut v_a_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(
        v_params_1455_,
        v_a_1456_,
        v_a_1457_,
        v_a_1458_,
        v_a_1459_,
        v_a_1460_,
    );
    return v___x_1462_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___boxed(
    mut v_pu_1463_: *mut crate::leanh::LeanObject,
    mut v_params_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
    mut v_a_1466_: *mut crate::leanh::LeanObject,
    mut v_a_1467_: *mut crate::leanh::LeanObject,
    mut v_a_1468_: *mut crate::leanh::LeanObject,
    mut v_a_1469_: *mut crate::leanh::LeanObject,
    mut v_a_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1471_: u8 = 0;
    let mut v_res_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1471_ = (crate::leanh::lean_unbox(v_pu_1463_) as u8);
    v_res_1472_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(
        v_pu_boxed_1471_,
        v_params_1464_,
        v_a_1465_,
        v_a_1466_,
        v_a_1467_,
        v_a_1468_,
        v_a_1469_,
    );
    crate::leanh::lean_dec(v_a_1469_);
    crate::leanh::lean_dec_ref(v_a_1468_);
    crate::leanh::lean_dec(v_a_1467_);
    crate::leanh::lean_dec_ref(v_a_1466_);
    crate::leanh::lean_dec(v_a_1465_);
    crate::leanh::lean_dec_ref(v_params_1464_);
    return v_res_1472_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(
    mut v_as_1473_: *mut crate::leanh::LeanObject,
    mut v_sz_1474_: usize,
    mut v_i_1475_: usize,
    mut v_b_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_1473_, v_sz_1474_, v_i_1475_, v_b_1476_, v___y_1477_);
    return v___x_1483_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___boxed(
    mut v_as_1484_: *mut crate::leanh::LeanObject,
    mut v_sz_1485_: *mut crate::leanh::LeanObject,
    mut v_i_1486_: *mut crate::leanh::LeanObject,
    mut v_b_1487_: *mut crate::leanh::LeanObject,
    mut v___y_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1494_: usize = 0;
    let mut v_i_boxed_1495_: usize = 0;
    let mut v_res_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1494_ = crate::leanh::lean_unbox_usize(v_sz_1485_);
    crate::leanh::lean_dec(v_sz_1485_);
    v_i_boxed_1495_ = crate::leanh::lean_unbox_usize(v_i_1486_);
    crate::leanh::lean_dec(v_i_1486_);
    v_res_1496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(v_as_1484_, v_sz_boxed_1494_, v_i_boxed_1495_, v_b_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
    crate::leanh::lean_dec(v___y_1492_);
    crate::leanh::lean_dec_ref(v___y_1491_);
    crate::leanh::lean_dec(v___y_1490_);
    crate::leanh::lean_dec_ref(v___y_1489_);
    crate::leanh::lean_dec(v___y_1488_);
    crate::leanh::lean_dec_ref(v_as_1484_);
    return v_res_1496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(
    mut v_p_1497_: *mut crate::leanh::LeanObject,
    mut v_k_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isFun_1499_: u8 = 0;
    v_isFun_1499_ = crate::leanh::lean_ctor_get_uint8(
        v_p_1497_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_isFun_1499_ == 0 {
        let mut v_decl_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_decl_1500_ = crate::leanh::lean_ctor_get(v_p_1497_, 0);
        crate::leanh::lean_inc_ref(v_decl_1500_);
        v___x_1501_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1501_, 0, v_decl_1500_);
        crate::leanh::lean_ctor_set(v___x_1501_, 1, v_k_1498_);
        return v___x_1501_;
    } else {
        let mut v_decl_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_decl_1502_ = crate::leanh::lean_ctor_get(v_p_1497_, 0);
        crate::leanh::lean_inc_ref(v_decl_1502_);
        v___x_1503_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1503_, 0, v_decl_1502_);
        crate::leanh::lean_ctor_set(v___x_1503_, 1, v_k_1498_);
        return v___x_1503_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach___boxed(
    mut v_p_1504_: *mut crate::leanh::LeanObject,
    mut v_k_1505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1506_ = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v_p_1504_, v_k_1505_);
    crate::leanh::lean_dec_ref(v_p_1504_);
    return v_res_1506_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(
    mut v_i_1507_: *mut crate::leanh::LeanObject,
    mut v_a_1508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_1509_ = crate::leanh::lean_ctor_get(v_a_1508_, 1);
    v___x_1510_ = 0;
    v___x_1511_ = crate::leanh::lean_box((v___x_1510_) as usize);
    v___x_1512_ = lean_array_get(v___x_1511_, v_snd_1509_, v_i_1507_);
    crate::leanh::lean_dec(v___x_1511_);
    v___x_1513_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1513_, 1, v_a_1508_);
    return v___x_1513_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited___boxed(
    mut v_i_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1516_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_1514_, v_a_1515_);
    crate::leanh::lean_dec(v_i_1514_);
    return v_res_1516_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(
    mut v_upperBound_1517_: *mut crate::leanh::LeanObject,
    mut v___x_1518_: *mut crate::leanh::LeanObject,
    mut v_ps_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
    mut v_b_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v_decl_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1529_ = lean_nat_dec_lt(v_a_1520_, v_upperBound_1517_);
                if v___x_1529_ == 0 {
                    crate::leanh::lean_dec(v_a_1520_);
                    v___x_1530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1530_, 0, v_b_1521_);
                    crate::leanh::lean_ctor_set(v___x_1530_, 1, v___y_1522_);
                    return v___x_1530_;
                } else {
                    v___x_1531_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_a_1520_, v___y_1522_);
                    v_fst_1532_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                    crate::leanh::lean_inc(v_fst_1532_);
                    v_snd_1533_ = crate::leanh::lean_ctor_get(v___x_1531_, 1);
                    crate::leanh::lean_inc(v_snd_1533_);
                    crate::leanh::lean_dec_ref(v___x_1531_);
                    v___x_1534_ = crate::leanh::lean_box(0);
                    v___x_1535_ = (crate::leanh::lean_unbox(v_fst_1532_) as u8);
                    crate::leanh::lean_dec(v_fst_1532_);
                    if v___x_1535_ == 0 {
                        v_decl_1536_ = crate::leanh::lean_ctor_get(v___x_1518_, 0);
                        v_fvarId_1537_ = crate::leanh::lean_ctor_get(v_decl_1536_, 0);
                        v___x_1538_ = lean_array_fget_borrowed(v_ps_1519_, v_a_1520_);
                        v_used_1539_ = crate::leanh::lean_ctor_get(v___x_1538_, 1);
                        v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_1539_, v_fvarId_1537_);
                        if v___x_1540_ == 0 {
                            v_a_1524_ = v___x_1534_;
                            v_snd_1525_ = v_snd_1533_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1541_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_1519_, v_a_1520_, v_snd_1533_);
                            v_snd_1542_ = crate::leanh::lean_ctor_get(v___x_1541_, 1);
                            crate::leanh::lean_inc(v_snd_1542_);
                            crate::leanh::lean_dec_ref(v___x_1541_);
                            v_a_1524_ = v___x_1534_;
                            v_snd_1525_ = v_snd_1542_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1524_ = v___x_1534_;
                        v_snd_1525_ = v_snd_1533_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1526_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1527_ = lean_nat_add(v_a_1520_, v___x_1526_);
                crate::leanh::lean_dec(v_a_1520_);
                v_a_1520_ = v___x_1527_;
                v_b_1521_ = v_a_1524_;
                v___y_1522_ = v_snd_1525_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(
    mut v_ps_1543_: *mut crate::leanh::LeanObject,
    mut v_i_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v_snd_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v_fst_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_isSharedCheck_1583_: u8 = 0;
    let mut v_unused_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut v_snd_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_unused_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1546_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_1544_, v_a_1545_);
                v_fst_1547_ = crate::leanh::lean_ctor_get(v___x_1546_, 0);
                crate::leanh::lean_inc(v_fst_1547_);
                v___x_1548_ = (crate::leanh::lean_unbox(v_fst_1547_) as u8);
                crate::leanh::lean_dec(v_fst_1547_);
                if v___x_1548_ == 0 {
                    v_snd_1549_ = crate::leanh::lean_ctor_get(v___x_1546_, 1);
                    crate::leanh::lean_inc(v_snd_1549_);
                    crate::leanh::lean_dec_ref(v___x_1546_);
                    v_fst_1550_ = crate::leanh::lean_ctor_get(v_snd_1549_, 0);
                    v_snd_1551_ = crate::leanh::lean_ctor_get(v_snd_1549_, 1);
                    v_isSharedCheck_1586_ = (!crate::leanh::lean_is_exclusive(v_snd_1549_)) as u8;
                    if v_isSharedCheck_1586_ == 0 {
                        v___x_1553_ = v_snd_1549_;
                        v_isShared_1554_ = v_isSharedCheck_1586_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1551_);
                        crate::leanh::lean_inc(v_fst_1550_);
                        crate::leanh::lean_dec(v_snd_1549_);
                        v___x_1553_ = crate::leanh::lean_box(0);
                        v_isShared_1554_ = v_isSharedCheck_1586_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_1587_ = crate::leanh::lean_ctor_get(v___x_1546_, 1);
                    v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v___x_1546_)) as u8;
                    if v_isSharedCheck_1595_ == 0 {
                        v_unused_1596_ = crate::leanh::lean_ctor_get(v___x_1546_, 0);
                        crate::leanh::lean_dec(v_unused_1596_);
                        v___x_1589_ = v___x_1546_;
                        v_isShared_1590_ = v_isSharedCheck_1595_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1587_);
                        crate::leanh::lean_dec(v___x_1546_);
                        v___x_1589_ = crate::leanh::lean_box(0);
                        v_isShared_1590_ = v_isSharedCheck_1595_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1555_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
                v___x_1556_ = lean_array_get_size(v_ps_1543_);
                v___x_1557_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1558_ = 1;
                v___x_1559_ = crate::leanh::lean_box((v___x_1558_) as usize);
                v___x_1560_ = lean_array_set(v_snd_1551_, v_i_1544_, v___x_1559_);
                v___x_1561_ = lean_array_get_borrowed(v___x_1555_, v_ps_1543_, v_i_1544_);
                if v_isShared_1554_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1553_, 1, v___x_1560_);
                    v___x_1563_ = v___x_1553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_fst_1550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1560_);
                    v___x_1563_ = v_reuseFailAlloc_1585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1564_ = crate::leanh::lean_box(0);
                v___x_1565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v___x_1556_, v___x_1561_, v_ps_1543_, v___x_1557_, v___x_1564_, v___x_1563_);
                v_snd_1566_ = crate::leanh::lean_ctor_get(v___x_1565_, 1);
                v_isSharedCheck_1583_ = (!crate::leanh::lean_is_exclusive(v___x_1565_)) as u8;
                if v_isSharedCheck_1583_ == 0 {
                    v_unused_1584_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                    crate::leanh::lean_dec(v_unused_1584_);
                    v___x_1568_ = v___x_1565_;
                    v_isShared_1569_ = v_isSharedCheck_1583_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1566_);
                    crate::leanh::lean_dec(v___x_1565_);
                    v___x_1568_ = crate::leanh::lean_box(0);
                    v_isShared_1569_ = v_isSharedCheck_1583_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_1570_ = crate::leanh::lean_ctor_get(v_snd_1566_, 0);
                v_snd_1571_ = crate::leanh::lean_ctor_get(v_snd_1566_, 1);
                v_isSharedCheck_1582_ = (!crate::leanh::lean_is_exclusive(v_snd_1566_)) as u8;
                if v_isSharedCheck_1582_ == 0 {
                    v___x_1573_ = v_snd_1566_;
                    v_isShared_1574_ = v_isSharedCheck_1582_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1571_);
                    crate::leanh::lean_inc(v_fst_1570_);
                    crate::leanh::lean_dec(v_snd_1566_);
                    v___x_1573_ = crate::leanh::lean_box(0);
                    v_isShared_1574_ = v_isSharedCheck_1582_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1575_ =
                    l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v___x_1561_, v_fst_1570_);
                if v_isShared_1574_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1573_, 0, v___x_1575_);
                    v___x_1577_ = v___x_1573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_snd_1571_);
                    v___x_1577_ = v_reuseFailAlloc_1581_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1568_, 1, v___x_1577_);
                    crate::leanh::lean_ctor_set(v___x_1568_, 0, v___x_1564_);
                    v___x_1579_ = v___x_1568_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___x_1577_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1579_;
            }
            7 => {
                v___x_1591_ = crate::leanh::lean_box(0);
                if v_isShared_1590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1589_, 0, v___x_1591_);
                    v___x_1593_ = v___x_1589_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_snd_1587_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit___boxed(
    mut v_ps_1597_: *mut crate::leanh::LeanObject,
    mut v_i_1598_: *mut crate::leanh::LeanObject,
    mut v_a_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ =
        l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(
            v_ps_1597_, v_i_1598_, v_a_1599_,
        );
    crate::leanh::lean_dec(v_i_1598_);
    crate::leanh::lean_dec_ref(v_ps_1597_);
    return v_res_1600_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg___boxed(
    mut v_upperBound_1601_: *mut crate::leanh::LeanObject,
    mut v___x_1602_: *mut crate::leanh::LeanObject,
    mut v_ps_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_b_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_1601_, v___x_1602_, v_ps_1603_, v_a_1604_, v_b_1605_, v___y_1606_);
    crate::leanh::lean_dec_ref(v_ps_1603_);
    crate::leanh::lean_dec_ref(v___x_1602_);
    crate::leanh::lean_dec(v_upperBound_1601_);
    return v_res_1607_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(
    mut v_upperBound_1608_: *mut crate::leanh::LeanObject,
    mut v___x_1609_: *mut crate::leanh::LeanObject,
    mut v_ps_1610_: *mut crate::leanh::LeanObject,
    mut v_inst_1611_: *mut crate::leanh::LeanObject,
    mut v_R_1612_: *mut crate::leanh::LeanObject,
    mut v_a_1613_: *mut crate::leanh::LeanObject,
    mut v_b_1614_: *mut crate::leanh::LeanObject,
    mut v_c_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_1608_, v___x_1609_, v_ps_1610_, v_a_1613_, v_b_1614_, v___y_1616_);
    return v___x_1617_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___boxed(
    mut v_upperBound_1618_: *mut crate::leanh::LeanObject,
    mut v___x_1619_: *mut crate::leanh::LeanObject,
    mut v_ps_1620_: *mut crate::leanh::LeanObject,
    mut v_inst_1621_: *mut crate::leanh::LeanObject,
    mut v_R_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_b_1624_: *mut crate::leanh::LeanObject,
    mut v_c_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(v_upperBound_1618_, v___x_1619_, v_ps_1620_, v_inst_1621_, v_R_1622_, v_a_1623_, v_b_1624_, v_c_1625_, v___y_1626_);
    crate::leanh::lean_dec_ref(v_ps_1620_);
    crate::leanh::lean_dec_ref(v___x_1619_);
    crate::leanh::lean_dec(v_upperBound_1618_);
    return v_res_1627_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(
    mut v_upperBound_1628_: *mut crate::leanh::LeanObject,
    mut v_ps_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
    mut v_b_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1633_ = lean_nat_dec_lt(v_a_1630_, v_upperBound_1628_);
                if v___x_1633_ == 0 {
                    crate::leanh::lean_dec(v_a_1630_);
                    v___x_1634_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v_b_1631_);
                    crate::leanh::lean_ctor_set(v___x_1634_, 1, v___y_1632_);
                    return v___x_1634_;
                } else {
                    v___x_1635_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_1629_, v_a_1630_, v___y_1632_);
                    v_snd_1636_ = crate::leanh::lean_ctor_get(v___x_1635_, 1);
                    crate::leanh::lean_inc(v_snd_1636_);
                    crate::leanh::lean_dec_ref(v___x_1635_);
                    v___x_1637_ = crate::leanh::lean_box(0);
                    v___x_1638_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1639_ = lean_nat_add(v_a_1630_, v___x_1638_);
                    crate::leanh::lean_dec(v_a_1630_);
                    v_a_1630_ = v___x_1639_;
                    v_b_1631_ = v___x_1637_;
                    v___y_1632_ = v_snd_1636_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg___boxed(
    mut v_upperBound_1641_: *mut crate::leanh::LeanObject,
    mut v_ps_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
    mut v_b_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_1641_, v_ps_1642_, v_a_1643_, v_b_1644_, v___y_1645_);
    crate::leanh::lean_dec_ref(v_ps_1642_);
    crate::leanh::lean_dec(v_upperBound_1641_);
    return v_res_1646_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(
    mut v_ps_1647_: *mut crate::leanh::LeanObject,
    mut v_a_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v_unused_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1649_ = lean_array_get_size(v_ps_1647_);
                v___x_1650_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1651_ = crate::leanh::lean_box(0);
                v___x_1652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v___x_1649_, v_ps_1647_, v___x_1650_, v___x_1651_, v_a_1648_);
                v_snd_1653_ = crate::leanh::lean_ctor_get(v___x_1652_, 1);
                v_isSharedCheck_1660_ = (!crate::leanh::lean_is_exclusive(v___x_1652_)) as u8;
                if v_isSharedCheck_1660_ == 0 {
                    v_unused_1661_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                    crate::leanh::lean_dec(v_unused_1661_);
                    v___x_1655_ = v___x_1652_;
                    v_isShared_1656_ = v_isSharedCheck_1660_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1653_);
                    crate::leanh::lean_dec(v___x_1652_);
                    v___x_1655_ = crate::leanh::lean_box(0);
                    v_isShared_1656_ = v_isSharedCheck_1660_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1651_);
                    v___x_1658_ = v___x_1655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_snd_1653_);
                    v___x_1658_ = v_reuseFailAlloc_1659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go___boxed(
    mut v_ps_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ =
        l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(
            v_ps_1662_, v_a_1663_,
        );
    crate::leanh::lean_dec_ref(v_ps_1662_);
    return v_res_1664_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(
    mut v_upperBound_1665_: *mut crate::leanh::LeanObject,
    mut v_ps_1666_: *mut crate::leanh::LeanObject,
    mut v_inst_1667_: *mut crate::leanh::LeanObject,
    mut v_R_1668_: *mut crate::leanh::LeanObject,
    mut v_a_1669_: *mut crate::leanh::LeanObject,
    mut v_b_1670_: *mut crate::leanh::LeanObject,
    mut v_c_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_1665_, v_ps_1666_, v_a_1669_, v_b_1670_, v___y_1672_);
    return v___x_1673_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___boxed(
    mut v_upperBound_1674_: *mut crate::leanh::LeanObject,
    mut v_ps_1675_: *mut crate::leanh::LeanObject,
    mut v_inst_1676_: *mut crate::leanh::LeanObject,
    mut v_R_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_b_1679_: *mut crate::leanh::LeanObject,
    mut v_c_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(v_upperBound_1674_, v_ps_1675_, v_inst_1676_, v_R_1677_, v_a_1678_, v_b_1679_, v_c_1680_, v___y_1681_);
    crate::leanh::lean_dec_ref(v_ps_1675_);
    crate::leanh::lean_dec(v_upperBound_1674_);
    return v_res_1682_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(
    mut v_sz_1683_: usize,
    mut v_i_1684_: usize,
    mut v_bs_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1690_: usize = 0;
    let mut v___x_1691_: usize = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1686_ = lean_usize_dec_lt(v_i_1684_, v_sz_1683_);
                if v___x_1686_ == 0 {
                    return v_bs_1685_;
                } else {
                    v___x_1687_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1688_ = lean_array_uset(v_bs_1685_, v_i_1684_, v___x_1687_);
                    v___x_1689_ = 0;
                    v___x_1690_ = 1usize;
                    v___x_1691_ = lean_usize_add(v_i_1684_, v___x_1690_);
                    v___x_1692_ = crate::leanh::lean_box((v___x_1689_) as usize);
                    v___x_1693_ = lean_array_uset(v_bs_x27_1688_, v_i_1684_, v___x_1692_);
                    v_i_1684_ = v___x_1691_;
                    v_bs_1685_ = v___x_1693_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0___boxed(
    mut v_sz_1695_: *mut crate::leanh::LeanObject,
    mut v_i_1696_: *mut crate::leanh::LeanObject,
    mut v_bs_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1698_: usize = 0;
    let mut v_i_boxed_1699_: usize = 0;
    let mut v_res_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1698_ = crate::leanh::lean_unbox_usize(v_sz_1695_);
    crate::leanh::lean_dec(v_sz_1695_);
    v_i_boxed_1699_ = crate::leanh::lean_unbox_usize(v_i_1696_);
    crate::leanh::lean_dec(v_i_1696_);
    v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_boxed_1698_, v_i_boxed_1699_, v_bs_1697_);
    return v_res_1700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attach(
    mut v_ps_1701_: *mut crate::leanh::LeanObject,
    mut v_k_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1703_: usize = 0;
    let mut v___x_1704_: usize = 0;
    let mut v_visited_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1703_ = lean_array_size(v_ps_1701_);
    v___x_1704_ = 0usize;
    crate::leanh::lean_inc_ref(v_ps_1701_);
    v_visited_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_1703_, v___x_1704_, v_ps_1701_);
    v___x_1706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1706_, 0, v_k_1702_);
    crate::leanh::lean_ctor_set(v___x_1706_, 1, v_visited_1705_);
    v___x_1707_ =
        l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(
            v_ps_1701_,
            v___x_1706_,
        );
    crate::leanh::lean_dec_ref(v_ps_1701_);
    v_snd_1708_ = crate::leanh::lean_ctor_get(v___x_1707_, 1);
    crate::leanh::lean_inc(v_snd_1708_);
    crate::leanh::lean_dec_ref(v___x_1707_);
    v_fst_1709_ = crate::leanh::lean_ctor_get(v_snd_1708_, 0);
    crate::leanh::lean_inc(v_fst_1709_);
    crate::leanh::lean_dec(v_snd_1708_);
    return v_fst_1709_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
    mut v_fvarId_1710_: *mut crate::leanh::LeanObject,
    mut v_k_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1714_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(
                    v_fvarId_1710_,
                    v_a_1712_,
                );
                if crate::leanh::lean_obj_tag(v___x_1714_) == 0 {
                    v_a_1715_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1723_ = (!crate::leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1723_ == 0 {
                        v___x_1717_ = v___x_1714_;
                        v_isShared_1718_ = v_isSharedCheck_1723_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1715_);
                        crate::leanh::lean_dec(v___x_1714_);
                        v___x_1717_ = crate::leanh::lean_box(0);
                        v_isShared_1718_ = v_isSharedCheck_1723_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_1711_);
                    v_a_1724_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1731_ = (!crate::leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1731_ == 0 {
                        v___x_1726_ = v___x_1714_;
                        v_isShared_1727_ = v_isSharedCheck_1731_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1724_);
                        crate::leanh::lean_dec(v___x_1714_);
                        v___x_1726_ = crate::leanh::lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1731_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1719_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_1715_, v_k_1711_);
                if v_isShared_1718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1719_);
                    v___x_1721_ = v___x_1717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1721_;
            }
            3 => {
                if v_isShared_1727_ == 0 {
                    v___x_1729_ = v___x_1726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
                    v___x_1729_ = v_reuseFailAlloc_1730_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg___boxed(
    mut v_fvarId_1732_: *mut crate::leanh::LeanObject,
    mut v_k_1733_: *mut crate::leanh::LeanObject,
    mut v_a_1734_: *mut crate::leanh::LeanObject,
    mut v_a_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
        v_fvarId_1732_,
        v_k_1733_,
        v_a_1734_,
    );
    crate::leanh::lean_dec(v_a_1734_);
    crate::leanh::lean_dec(v_fvarId_1732_);
    return v_res_1736_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(
    mut v_fvarId_1737_: *mut crate::leanh::LeanObject,
    mut v_k_1738_: *mut crate::leanh::LeanObject,
    mut v_a_1739_: *mut crate::leanh::LeanObject,
    mut v_a_1740_: *mut crate::leanh::LeanObject,
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v_a_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
        v_fvarId_1737_,
        v_k_1738_,
        v_a_1739_,
    );
    return v___x_1745_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___boxed(
    mut v_fvarId_1746_: *mut crate::leanh::LeanObject,
    mut v_k_1747_: *mut crate::leanh::LeanObject,
    mut v_a_1748_: *mut crate::leanh::LeanObject,
    mut v_a_1749_: *mut crate::leanh::LeanObject,
    mut v_a_1750_: *mut crate::leanh::LeanObject,
    mut v_a_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(
        v_fvarId_1746_,
        v_k_1747_,
        v_a_1748_,
        v_a_1749_,
        v_a_1750_,
        v_a_1751_,
        v_a_1752_,
    );
    crate::leanh::lean_dec(v_a_1752_);
    crate::leanh::lean_dec_ref(v_a_1751_);
    crate::leanh::lean_dec(v_a_1750_);
    crate::leanh::lean_dec_ref(v_a_1749_);
    crate::leanh::lean_dec(v_a_1748_);
    crate::leanh::lean_dec(v_fvarId_1746_);
    return v_res_1754_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
    mut v_params_1755_: *mut crate::leanh::LeanObject,
    mut v_k_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1772_: u8 = 0;
    let mut v_a_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1763_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(
                    v_params_1755_,
                    v_a_1757_,
                    v_a_1758_,
                    v_a_1759_,
                    v_a_1760_,
                    v_a_1761_,
                );
                if crate::leanh::lean_obj_tag(v___x_1763_) == 0 {
                    v_a_1764_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1772_ = (!crate::leanh::lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1772_ == 0 {
                        v___x_1766_ = v___x_1763_;
                        v_isShared_1767_ = v_isSharedCheck_1772_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1764_);
                        crate::leanh::lean_dec(v___x_1763_);
                        v___x_1766_ = crate::leanh::lean_box(0);
                        v_isShared_1767_ = v_isSharedCheck_1772_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_1756_);
                    v_a_1773_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1780_ = (!crate::leanh::lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1780_ == 0 {
                        v___x_1775_ = v___x_1763_;
                        v_isShared_1776_ = v_isSharedCheck_1780_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1773_);
                        crate::leanh::lean_dec(v___x_1763_);
                        v___x_1775_ = crate::leanh::lean_box(0);
                        v_isShared_1776_ = v_isSharedCheck_1780_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1768_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_1764_, v_k_1756_);
                if v_isShared_1767_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
                    v___x_1770_ = v_reuseFailAlloc_1771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1770_;
            }
            3 => {
                if v_isShared_1776_ == 0 {
                    v___x_1778_ = v___x_1775_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
                    v___x_1778_ = v_reuseFailAlloc_1779_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps___boxed(
    mut v_params_1781_: *mut crate::leanh::LeanObject,
    mut v_k_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
        v_params_1781_,
        v_k_1782_,
        v_a_1783_,
        v_a_1784_,
        v_a_1785_,
        v_a_1786_,
        v_a_1787_,
    );
    crate::leanh::lean_dec(v_a_1787_);
    crate::leanh::lean_dec_ref(v_a_1786_);
    crate::leanh::lean_dec(v_a_1785_);
    crate::leanh::lean_dec_ref(v_a_1784_);
    crate::leanh::lean_dec(v_a_1783_);
    crate::leanh::lean_dec_ref(v_params_1781_);
    return v_res_1789_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isFun_1794_: u8 = 0;
    let mut v_tail_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v_unused_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1790_) == 0 {
                    v___x_1792_ = l_List_reverse___redArg(v_a_1791_);
                    return v___x_1792_;
                } else {
                    v_head_1793_ = crate::leanh::lean_ctor_get(v_a_1790_, 0);
                    v_isFun_1794_ = crate::leanh::lean_ctor_get_uint8(
                        v_head_1793_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    if v_isFun_1794_ == 0 {
                        crate::leanh::lean_inc(v_head_1793_);
                        v_tail_1795_ = crate::leanh::lean_ctor_get(v_a_1790_, 1);
                        v_isSharedCheck_1803_ = (!crate::leanh::lean_is_exclusive(v_a_1790_)) as u8;
                        if v_isSharedCheck_1803_ == 0 {
                            v_unused_1804_ = crate::leanh::lean_ctor_get(v_a_1790_, 0);
                            crate::leanh::lean_dec(v_unused_1804_);
                            v___x_1797_ = v_a_1790_;
                            v_isShared_1798_ = v_isSharedCheck_1803_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_1795_);
                            crate::leanh::lean_dec(v_a_1790_);
                            v___x_1797_ = crate::leanh::lean_box(0);
                            v_isShared_1798_ = v_isSharedCheck_1803_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_tail_1805_ = crate::leanh::lean_ctor_get(v_a_1790_, 1);
                        crate::leanh::lean_inc(v_tail_1805_);
                        crate::leanh::lean_dec_ref_known(v_a_1790_, 2);
                        v_a_1790_ = v_tail_1805_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1797_, 1, v_a_1791_);
                    v___x_1800_ = v___x_1797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_head_1793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_a_1791_);
                    v___x_1800_ = v_reuseFailAlloc_1802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1790_ = v_tail_1795_;
                v_a_1791_ = v___x_1800_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__0(
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isFun_1811_: u8 = 0;
    let mut v_tail_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v_unused_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1807_) == 0 {
                    v___x_1809_ = l_List_reverse___redArg(v_a_1808_);
                    return v___x_1809_;
                } else {
                    v_head_1810_ = crate::leanh::lean_ctor_get(v_a_1807_, 0);
                    v_isFun_1811_ = crate::leanh::lean_ctor_get_uint8(
                        v_head_1810_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    if v_isFun_1811_ == 0 {
                        v_tail_1812_ = crate::leanh::lean_ctor_get(v_a_1807_, 1);
                        crate::leanh::lean_inc(v_tail_1812_);
                        crate::leanh::lean_dec_ref_known(v_a_1807_, 2);
                        v_a_1807_ = v_tail_1812_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_head_1810_);
                        v_tail_1814_ = crate::leanh::lean_ctor_get(v_a_1807_, 1);
                        v_isSharedCheck_1822_ = (!crate::leanh::lean_is_exclusive(v_a_1807_)) as u8;
                        if v_isSharedCheck_1822_ == 0 {
                            v_unused_1823_ = crate::leanh::lean_ctor_get(v_a_1807_, 0);
                            crate::leanh::lean_dec(v_unused_1823_);
                            v___x_1816_ = v_a_1807_;
                            v_isShared_1817_ = v_isSharedCheck_1822_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_1814_);
                            crate::leanh::lean_dec(v_a_1807_);
                            v___x_1816_ = crate::leanh::lean_box(0);
                            v_isShared_1817_ = v_isSharedCheck_1822_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1817_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1816_, 1, v_a_1808_);
                    v___x_1819_ = v___x_1816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_head_1810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_a_1808_);
                    v___x_1819_ = v_reuseFailAlloc_1821_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1807_ = v_tail_1814_;
                v_a_1808_ = v___x_1819_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(
    mut v_k_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_a_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1827_ = lean_st_ref_get(v_a_1825_);
                v___x_1828_ = lean_st_ref_take(v_a_1825_);
                v___x_1829_ = crate::leanh::lean_box(0);
                v___x_1830_ =
                    l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__0(
                        v___x_1828_,
                        v___x_1829_,
                    );
                v___x_1831_ = lean_st_ref_set(v_a_1825_, v___x_1830_);
                v___x_1832_ =
                    l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(
                        v___x_1827_,
                        v___x_1829_,
                    );
                v___x_1833_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0;
                v___x_1834_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
                    v___x_1832_,
                    v___x_1833_,
                    v_a_1825_,
                );
                if crate::leanh::lean_obj_tag(v___x_1834_) == 0 {
                    v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                    v_isSharedCheck_1843_ = (!crate::leanh::lean_is_exclusive(v___x_1834_)) as u8;
                    if v_isSharedCheck_1843_ == 0 {
                        v___x_1837_ = v___x_1834_;
                        v_isShared_1838_ = v_isSharedCheck_1843_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1835_);
                        crate::leanh::lean_dec(v___x_1834_);
                        v___x_1837_ = crate::leanh::lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1843_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_1824_);
                    v_a_1844_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                    v_isSharedCheck_1851_ = (!crate::leanh::lean_is_exclusive(v___x_1834_)) as u8;
                    if v_isSharedCheck_1851_ == 0 {
                        v___x_1846_ = v___x_1834_;
                        v_isShared_1847_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1844_);
                        crate::leanh::lean_dec(v___x_1834_);
                        v___x_1846_ = crate::leanh::lean_box(0);
                        v_isShared_1847_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1839_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_1835_, v_k_1824_);
                if v_isShared_1838_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1839_);
                    v___x_1841_ = v___x_1837_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
                    v___x_1841_ = v_reuseFailAlloc_1842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1841_;
            }
            3 => {
                if v_isShared_1847_ == 0 {
                    v___x_1849_ = v___x_1846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
                    v___x_1849_ = v_reuseFailAlloc_1850_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg___boxed(
    mut v_k_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_1852_, v_a_1853_);
    crate::leanh::lean_dec(v_a_1853_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachJps(
    mut v_k_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
    mut v_a_1859_: *mut crate::leanh::LeanObject,
    mut v_a_1860_: *mut crate::leanh::LeanObject,
    mut v_a_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_1856_, v_a_1857_);
    return v___x_1863_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachJps___boxed(
    mut v_k_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_a_1866_: *mut crate::leanh::LeanObject,
    mut v_a_1867_: *mut crate::leanh::LeanObject,
    mut v_a_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
    mut v_a_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps(
        v_k_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_,
    );
    crate::leanh::lean_dec(v_a_1869_);
    crate::leanh::lean_dec_ref(v_a_1868_);
    crate::leanh::lean_dec(v_a_1867_);
    crate::leanh::lean_dec_ref(v_a_1866_);
    crate::leanh::lean_dec(v_a_1865_);
    return v_res_1871_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_addToPull(
    mut v_isFun_1872_: u8,
    mut v_decl_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
    mut v_a_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
    mut v_a_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v_value_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut v_a_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_a_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut v_a_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = lean_st_ref_get(v_a_1874_);
                v___x_1881_ = lean_st_ref_take(v_a_1874_);
                crate::leanh::lean_dec(v___x_1881_);
                v___x_1882_ = crate::leanh::lean_box(0);
                v___x_1883_ = lean_st_ref_set(v_a_1874_, v___x_1882_);
                v_params_1884_ = crate::leanh::lean_ctor_get(v_decl_1873_, 2);
                crate::leanh::lean_inc_ref(v_params_1884_);
                v_type_1885_ = crate::leanh::lean_ctor_get(v_decl_1873_, 3);
                crate::leanh::lean_inc_ref(v_type_1885_);
                v_value_1886_ = crate::leanh::lean_ctor_get(v_decl_1873_, 4);
                crate::leanh::lean_inc_ref(v_value_1886_);
                v___x_1887_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                    v_value_1886_,
                    v_a_1874_,
                    v_a_1875_,
                    v_a_1876_,
                    v_a_1877_,
                    v_a_1878_,
                );
                if crate::leanh::lean_obj_tag(v___x_1887_) == 0 {
                    v_a_1888_ = crate::leanh::lean_ctor_get(v___x_1887_, 0);
                    crate::leanh::lean_inc(v_a_1888_);
                    crate::leanh::lean_dec_ref_known(v___x_1887_, 1);
                    v___x_1889_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
                        v_params_1884_,
                        v_a_1888_,
                        v_a_1874_,
                        v_a_1875_,
                        v_a_1876_,
                        v_a_1877_,
                        v_a_1878_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1889_) == 0 {
                        v_a_1890_ = crate::leanh::lean_ctor_get(v___x_1889_, 0);
                        crate::leanh::lean_inc(v_a_1890_);
                        crate::leanh::lean_dec_ref_known(v___x_1889_, 1);
                        v___x_1891_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                        v___x_1892_ = 0;
                        if v_isFun_1872_ == 0 {
                            v_value_1894_ = v_a_1890_;
                            v___y_1895_ = v_a_1874_;
                            v___y_1896_ = v_a_1876_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1921_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(
                                v_a_1890_, v_a_1874_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1921_) == 0 {
                                v_a_1922_ = crate::leanh::lean_ctor_get(v___x_1921_, 0);
                                crate::leanh::lean_inc(v_a_1922_);
                                crate::leanh::lean_dec_ref_known(v___x_1921_, 1);
                                v_value_1894_ = v_a_1922_;
                                v___y_1895_ = v_a_1874_;
                                v___y_1896_ = v_a_1876_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_type_1885_);
                                crate::leanh::lean_dec_ref(v_params_1884_);
                                crate::leanh::lean_dec(v___x_1880_);
                                crate::leanh::lean_dec_ref(v_decl_1873_);
                                v_a_1923_ = crate::leanh::lean_ctor_get(v___x_1921_, 0);
                                v_isSharedCheck_1930_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1921_)) as u8;
                                if v_isSharedCheck_1930_ == 0 {
                                    v___x_1925_ = v___x_1921_;
                                    v_isShared_1926_ = v_isSharedCheck_1930_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1923_);
                                    crate::leanh::lean_dec(v___x_1921_);
                                    v___x_1925_ = crate::leanh::lean_box(0);
                                    v_isShared_1926_ = v_isSharedCheck_1930_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_1885_);
                        crate::leanh::lean_dec_ref(v_params_1884_);
                        crate::leanh::lean_dec(v___x_1880_);
                        crate::leanh::lean_dec_ref(v_decl_1873_);
                        v_a_1931_ = crate::leanh::lean_ctor_get(v___x_1889_, 0);
                        v_isSharedCheck_1938_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1889_)) as u8;
                        if v_isSharedCheck_1938_ == 0 {
                            v___x_1933_ = v___x_1889_;
                            v_isShared_1934_ = v_isSharedCheck_1938_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1931_);
                            crate::leanh::lean_dec(v___x_1889_);
                            v___x_1933_ = crate::leanh::lean_box(0);
                            v_isShared_1934_ = v_isSharedCheck_1938_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_1885_);
                    crate::leanh::lean_dec_ref(v_params_1884_);
                    crate::leanh::lean_dec(v___x_1880_);
                    crate::leanh::lean_dec_ref(v_decl_1873_);
                    v_a_1939_ = crate::leanh::lean_ctor_get(v___x_1887_, 0);
                    v_isSharedCheck_1946_ = (!crate::leanh::lean_is_exclusive(v___x_1887_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1941_ = v___x_1887_;
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1939_);
                        crate::leanh::lean_dec(v___x_1887_);
                        v___x_1941_ = crate::leanh::lean_box(0);
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1897_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1892_, v_decl_1873_, v_type_1885_, v_params_1884_, v_value_1894_, v___y_1896_);
                if crate::leanh::lean_obj_tag(v___x_1897_) == 0 {
                    v_a_1898_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1912_ = (!crate::leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1912_ == 0 {
                        v___x_1900_ = v___x_1897_;
                        v_isShared_1901_ = v_isSharedCheck_1912_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1898_);
                        crate::leanh::lean_dec(v___x_1897_);
                        v___x_1900_ = crate::leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1912_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1880_);
                    v_a_1913_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1920_ = (!crate::leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1920_ == 0 {
                        v___x_1915_ = v___x_1897_;
                        v_isShared_1916_ = v_isSharedCheck_1920_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1913_);
                        crate::leanh::lean_dec(v___x_1897_);
                        v___x_1915_ = crate::leanh::lean_box(0);
                        v_isShared_1916_ = v_isSharedCheck_1920_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1902_ = lean_st_ref_take(v___y_1895_);
                crate::leanh::lean_inc(v_a_1898_);
                v___x_1903_ =
                    l_Lean_Compiler_LCNF_FunDecl_collectUsed(v___x_1892_, v_a_1898_, v___x_1891_);
                v___x_1904_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1904_, 0, v_a_1898_);
                crate::leanh::lean_ctor_set(v___x_1904_, 1, v___x_1903_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1904_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_isFun_1872_,
                );
                v___x_1905_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1902_);
                v___x_1906_ = l_List_appendTR___redArg(v___x_1905_, v___x_1880_);
                v___x_1907_ = lean_st_ref_set(v___y_1895_, v___x_1906_);
                v___x_1908_ = crate::leanh::lean_box(0);
                if v_isShared_1901_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1908_);
                    v___x_1910_ = v___x_1900_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
                    v___x_1910_ = v_reuseFailAlloc_1911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1910_;
            }
            4 => {
                if v_isShared_1916_ == 0 {
                    v___x_1918_ = v___x_1915_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1918_;
            }
            6 => {
                if v_isShared_1926_ == 0 {
                    v___x_1928_ = v___x_1925_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
                    v___x_1928_ = v_reuseFailAlloc_1929_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1928_;
            }
            8 => {
                if v_isShared_1934_ == 0 {
                    v___x_1936_ = v___x_1933_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1937_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
                    v___x_1936_ = v_reuseFailAlloc_1937_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1936_;
            }
            10 => {
                if v_isShared_1942_ == 0 {
                    v___x_1944_ = v___x_1941_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
                    v___x_1944_ = v_reuseFailAlloc_1945_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_pull(
    mut v_code_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___y_1965_: u8 = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut v_unused_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: usize = 0;
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: u8 = 0;
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_decl_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_decl_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2012_: u8 = 0;
    let mut v_cases_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: usize = 0;
    let mut v___x_2028_: usize = 0;
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut v_unused_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v_a_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_1947_) {
                0 => {
                    v_decl_1954_ = crate::leanh::lean_ctor_get(v_code_1947_, 0);
                    v_k_1955_ = crate::leanh::lean_ctor_get(v_code_1947_, 1);
                    crate::leanh::lean_inc_ref(v_k_1955_);
                    v___x_1956_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                        v_k_1955_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1956_) == 0 {
                        v_a_1957_ = crate::leanh::lean_ctor_get(v___x_1956_, 0);
                        crate::leanh::lean_inc(v_a_1957_);
                        crate::leanh::lean_dec_ref_known(v___x_1956_, 1);
                        v_fvarId_1958_ = crate::leanh::lean_ctor_get(v_decl_1954_, 0);
                        v___x_1959_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
                            v_fvarId_1958_,
                            v_a_1957_,
                            v_a_1948_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1959_) == 0 {
                            v_a_1960_ = crate::leanh::lean_ctor_get(v___x_1959_, 0);
                            v_isSharedCheck_1986_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1959_)) as u8;
                            if v_isSharedCheck_1986_ == 0 {
                                v___x_1962_ = v___x_1959_;
                                v_isShared_1963_ = v_isSharedCheck_1986_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1960_);
                                crate::leanh::lean_dec(v___x_1959_);
                                v___x_1962_ = crate::leanh::lean_box(0);
                                v_isShared_1963_ = v_isSharedCheck_1986_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1947_, 2);
                            return v___x_1959_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1947_, 2);
                        return v___x_1956_;
                    }
                }
                1 => {
                    v_decl_1987_ = crate::leanh::lean_ctor_get(v_code_1947_, 0);
                    crate::leanh::lean_inc_ref(v_decl_1987_);
                    v_k_1988_ = crate::leanh::lean_ctor_get(v_code_1947_, 1);
                    crate::leanh::lean_inc_ref(v_k_1988_);
                    crate::leanh::lean_dec_ref_known(v_code_1947_, 2);
                    v___x_1989_ = 1;
                    v___x_1990_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(
                        v___x_1989_,
                        v_decl_1987_,
                        v_a_1948_,
                        v_a_1949_,
                        v_a_1950_,
                        v_a_1951_,
                        v_a_1952_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1990_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1990_, 1);
                        v_code_1947_ = v_k_1988_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_1988_);
                        v_a_1992_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                        v_isSharedCheck_1999_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_1999_ == 0 {
                            v___x_1994_ = v___x_1990_;
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1992_);
                            crate::leanh::lean_dec(v___x_1990_);
                            v___x_1994_ = crate::leanh::lean_box(0);
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 7;
                            continue;
                        }
                    }
                }
                2 => {
                    v_decl_2000_ = crate::leanh::lean_ctor_get(v_code_1947_, 0);
                    crate::leanh::lean_inc_ref(v_decl_2000_);
                    v_k_2001_ = crate::leanh::lean_ctor_get(v_code_1947_, 1);
                    crate::leanh::lean_inc_ref(v_k_2001_);
                    crate::leanh::lean_dec_ref_known(v_code_1947_, 2);
                    v___x_2002_ = 0;
                    v___x_2003_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(
                        v___x_2002_,
                        v_decl_2000_,
                        v_a_1948_,
                        v_a_1949_,
                        v_a_1950_,
                        v_a_1951_,
                        v_a_1952_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2003_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2003_, 1);
                        v_code_1947_ = v_k_2001_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_2001_);
                        v_a_2005_ = crate::leanh::lean_ctor_get(v___x_2003_, 0);
                        v_isSharedCheck_2012_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2003_)) as u8;
                        if v_isSharedCheck_2012_ == 0 {
                            v___x_2007_ = v___x_2003_;
                            v_isShared_2008_ = v_isSharedCheck_2012_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2005_);
                            crate::leanh::lean_dec(v___x_2003_);
                            v___x_2007_ = crate::leanh::lean_box(0);
                            v_isShared_2008_ = v_isSharedCheck_2012_;
                            state = 9;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_2013_ = crate::leanh::lean_ctor_get(v_code_1947_, 0);
                    crate::leanh::lean_inc_ref(v_cases_2013_);
                    v_typeName_2014_ = crate::leanh::lean_ctor_get(v_cases_2013_, 0);
                    v_resultType_2015_ = crate::leanh::lean_ctor_get(v_cases_2013_, 1);
                    v_discr_2016_ = crate::leanh::lean_ctor_get(v_cases_2013_, 2);
                    v_alts_2017_ = crate::leanh::lean_ctor_get(v_cases_2013_, 3);
                    v_isSharedCheck_2056_ = (!crate::leanh::lean_is_exclusive(v_cases_2013_)) as u8;
                    if v_isSharedCheck_2056_ == 0 {
                        v___x_2019_ = v_cases_2013_;
                        v_isShared_2020_ = v_isSharedCheck_2056_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_2017_);
                        crate::leanh::lean_inc(v_discr_2016_);
                        crate::leanh::lean_inc(v_resultType_2015_);
                        crate::leanh::lean_inc(v_typeName_2014_);
                        crate::leanh::lean_dec(v_cases_2013_);
                        v___x_2019_ = crate::leanh::lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2056_;
                        state = 11;
                        continue;
                    }
                }
                _ => {
                    v___x_2057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2057_, 0, v_code_1947_);
                    return v___x_2057_;
                }
            },
            1 => {
                v___x_1981_ = lean_ptr_addr(v_k_1955_);
                v___x_1982_ = lean_ptr_addr(v_a_1960_);
                v___x_1983_ = lean_usize_dec_eq(v___x_1981_, v___x_1982_);
                if v___x_1983_ == 0 {
                    v___y_1965_ = v___x_1983_;
                    state = 2;
                    continue;
                } else {
                    v___x_1984_ = lean_ptr_addr(v_decl_1954_);
                    v___x_1985_ = lean_usize_dec_eq(v___x_1984_, v___x_1984_);
                    v___y_1965_ = v___x_1985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_1965_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_1954_);
                    v_isSharedCheck_1975_ = (!crate::leanh::lean_is_exclusive(v_code_1947_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v_unused_1976_ = crate::leanh::lean_ctor_get(v_code_1947_, 1);
                        crate::leanh::lean_dec(v_unused_1976_);
                        v_unused_1977_ = crate::leanh::lean_ctor_get(v_code_1947_, 0);
                        crate::leanh::lean_dec(v_unused_1977_);
                        v___x_1967_ = v_code_1947_;
                        v_isShared_1968_ = v_isSharedCheck_1975_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1947_);
                        v___x_1967_ = crate::leanh::lean_box(0);
                        v_isShared_1968_ = v_isSharedCheck_1975_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1960_);
                    if v_isShared_1963_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1962_, 0, v_code_1947_);
                        v___x_1979_ = v___x_1962_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_code_1947_);
                        v___x_1979_ = v_reuseFailAlloc_1980_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1967_, 1, v_a_1960_);
                    v___x_1970_ = v___x_1967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_decl_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_a_1960_);
                    v___x_1970_ = v_reuseFailAlloc_1974_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1970_);
                    v___x_1972_ = v___x_1962_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1972_;
            }
            6 => {
                return v___x_1979_;
            }
            7 => {
                if v_isShared_1995_ == 0 {
                    v___x_1997_ = v___x_1994_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_1998_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1997_;
            }
            9 => {
                if v_isShared_2008_ == 0 {
                    v___x_2010_ = v___x_2007_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
                    v___x_2010_ = v_reuseFailAlloc_2011_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2010_;
            }
            11 => {
                v___x_2021_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_2017_);
                v___x_2022_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v___x_2021_, v_alts_2017_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
                if crate::leanh::lean_obj_tag(v___x_2022_) == 0 {
                    v_a_2023_ = crate::leanh::lean_ctor_get(v___x_2022_, 0);
                    v_isSharedCheck_2047_ = (!crate::leanh::lean_is_exclusive(v___x_2022_)) as u8;
                    if v_isSharedCheck_2047_ == 0 {
                        v___x_2025_ = v___x_2022_;
                        v_isShared_2026_ = v_isSharedCheck_2047_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2023_);
                        crate::leanh::lean_dec(v___x_2022_);
                        v___x_2025_ = crate::leanh::lean_box(0);
                        v_isShared_2026_ = v_isSharedCheck_2047_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2019_);
                    crate::leanh::lean_dec_ref(v_alts_2017_);
                    crate::leanh::lean_dec(v_discr_2016_);
                    crate::leanh::lean_dec_ref(v_resultType_2015_);
                    crate::leanh::lean_dec(v_typeName_2014_);
                    crate::leanh::lean_dec_ref_known(v_code_1947_, 1);
                    v_a_2048_ = crate::leanh::lean_ctor_get(v___x_2022_, 0);
                    v_isSharedCheck_2055_ = (!crate::leanh::lean_is_exclusive(v___x_2022_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v___x_2050_ = v___x_2022_;
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2048_);
                        crate::leanh::lean_dec(v___x_2022_);
                        v___x_2050_ = crate::leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 18;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2027_ = lean_ptr_addr(v_alts_2017_);
                crate::leanh::lean_dec_ref(v_alts_2017_);
                v___x_2028_ = lean_ptr_addr(v_a_2023_);
                v___x_2029_ = lean_usize_dec_eq(v___x_2027_, v___x_2028_);
                if v___x_2029_ == 0 {
                    v_isSharedCheck_2042_ = (!crate::leanh::lean_is_exclusive(v_code_1947_)) as u8;
                    if v_isSharedCheck_2042_ == 0 {
                        v_unused_2043_ = crate::leanh::lean_ctor_get(v_code_1947_, 0);
                        crate::leanh::lean_dec(v_unused_2043_);
                        v___x_2031_ = v_code_1947_;
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1947_);
                        v___x_2031_ = crate::leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2023_);
                    crate::leanh::lean_del_object(v___x_2019_);
                    crate::leanh::lean_dec(v_discr_2016_);
                    crate::leanh::lean_dec_ref(v_resultType_2015_);
                    crate::leanh::lean_dec(v_typeName_2014_);
                    if v_isShared_2026_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2025_, 0, v_code_1947_);
                        v___x_2045_ = v___x_2025_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_code_1947_);
                        v___x_2045_ = v_reuseFailAlloc_2046_;
                        state = 17;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_2020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2019_, 3, v_a_2023_);
                    v___x_2034_ = v___x_2019_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_typeName_2014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_resultType_2015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_discr_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_a_2023_);
                    v___x_2034_ = v_reuseFailAlloc_2041_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2034_);
                    v___x_2036_ = v___x_2031_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2034_);
                    v___x_2036_ = v_reuseFailAlloc_2040_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2036_);
                    v___x_2038_ = v___x_2025_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
                    v___x_2038_ = v_reuseFailAlloc_2039_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2038_;
            }
            17 => {
                return v___x_2045_;
            }
            18 => {
                if v_isShared_2051_ == 0 {
                    v___x_2053_ = v___x_2050_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(
    mut v_i_2058_: *mut crate::leanh::LeanObject,
    mut v_as_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
    mut v___y_2063_: *mut crate::leanh::LeanObject,
    mut v___y_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: usize = 0;
    let mut v___x_2073_: usize = 0;
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2092_: u8 = 0;
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v_a_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut v_code_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2066_ = lean_array_get_size(v_as_2059_);
                v___x_2067_ = lean_nat_dec_lt(v_i_2058_, v___x_2066_);
                if v___x_2067_ == 0 {
                    crate::leanh::lean_dec(v_i_2058_);
                    v___x_2068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2068_, 0, v_as_2059_);
                    return v___x_2068_;
                } else {
                    v_a_2069_ = lean_array_fget_borrowed(v_as_2059_, v_i_2058_);
                    if crate::leanh::lean_obj_tag(v_a_2069_) == 0 {
                        v_params_2082_ = crate::leanh::lean_ctor_get(v_a_2069_, 1);
                        v_code_2083_ = crate::leanh::lean_ctor_get(v_a_2069_, 2);
                        crate::leanh::lean_inc_ref(v_code_2083_);
                        v___x_2084_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                            v_code_2083_,
                            v___y_2060_,
                            v___y_2061_,
                            v___y_2062_,
                            v___y_2063_,
                            v___y_2064_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2084_) == 0 {
                            v_a_2085_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                            crate::leanh::lean_inc(v_a_2085_);
                            crate::leanh::lean_dec_ref_known(v___x_2084_, 1);
                            v___x_2086_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
                                v_params_2082_,
                                v_a_2085_,
                                v___y_2060_,
                                v___y_2061_,
                                v___y_2062_,
                                v___y_2063_,
                                v___y_2064_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2086_) == 0 {
                                v_a_2087_ = crate::leanh::lean_ctor_get(v___x_2086_, 0);
                                crate::leanh::lean_inc(v_a_2087_);
                                crate::leanh::lean_dec_ref_known(v___x_2086_, 1);
                                crate::leanh::lean_inc_ref(v_a_2069_);
                                v___x_2088_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2069_, v_a_2087_);
                                v_a_2071_ = v___x_2088_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_as_2059_);
                                crate::leanh::lean_dec(v_i_2058_);
                                v_a_2089_ = crate::leanh::lean_ctor_get(v___x_2086_, 0);
                                v_isSharedCheck_2096_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2086_)) as u8;
                                if v_isSharedCheck_2096_ == 0 {
                                    v___x_2091_ = v___x_2086_;
                                    v_isShared_2092_ = v_isSharedCheck_2096_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2089_);
                                    crate::leanh::lean_dec(v___x_2086_);
                                    v___x_2091_ = crate::leanh::lean_box(0);
                                    v_isShared_2092_ = v_isSharedCheck_2096_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_as_2059_);
                            crate::leanh::lean_dec(v_i_2058_);
                            v_a_2097_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                            v_isSharedCheck_2104_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2084_)) as u8;
                            if v_isSharedCheck_2104_ == 0 {
                                v___x_2099_ = v___x_2084_;
                                v_isShared_2100_ = v_isSharedCheck_2104_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2097_);
                                crate::leanh::lean_dec(v___x_2084_);
                                v___x_2099_ = crate::leanh::lean_box(0);
                                v_isShared_2100_ = v_isSharedCheck_2104_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_code_2105_ = crate::leanh::lean_ctor_get(v_a_2069_, 0);
                        crate::leanh::lean_inc_ref(v_code_2105_);
                        v___x_2106_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                            v_code_2105_,
                            v___y_2060_,
                            v___y_2061_,
                            v___y_2062_,
                            v___y_2063_,
                            v___y_2064_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2106_) == 0 {
                            v_a_2107_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                            crate::leanh::lean_inc(v_a_2107_);
                            crate::leanh::lean_dec_ref_known(v___x_2106_, 1);
                            crate::leanh::lean_inc_ref(v_a_2069_);
                            v___x_2108_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2069_, v_a_2107_);
                            v_a_2071_ = v___x_2108_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_as_2059_);
                            crate::leanh::lean_dec(v_i_2058_);
                            v_a_2109_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                            v_isSharedCheck_2116_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2106_)) as u8;
                            if v_isSharedCheck_2116_ == 0 {
                                v___x_2111_ = v___x_2106_;
                                v_isShared_2112_ = v_isSharedCheck_2116_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2109_);
                                crate::leanh::lean_dec(v___x_2106_);
                                v___x_2111_ = crate::leanh::lean_box(0);
                                v_isShared_2112_ = v_isSharedCheck_2116_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2072_ = lean_ptr_addr(v_a_2069_);
                v___x_2073_ = lean_ptr_addr(v_a_2071_);
                v___x_2074_ = lean_usize_dec_eq(v___x_2072_, v___x_2073_);
                if v___x_2074_ == 0 {
                    v___x_2075_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2076_ = lean_nat_add(v_i_2058_, v___x_2075_);
                    v___x_2077_ = lean_array_fset(v_as_2059_, v_i_2058_, v_a_2071_);
                    crate::leanh::lean_dec(v_i_2058_);
                    v_i_2058_ = v___x_2076_;
                    v_as_2059_ = v___x_2077_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_2071_);
                    v___x_2079_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2080_ = lean_nat_add(v_i_2058_, v___x_2079_);
                    crate::leanh::lean_dec(v_i_2058_);
                    v_i_2058_ = v___x_2080_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_2092_ == 0 {
                    v___x_2094_ = v___x_2091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
                    v___x_2094_ = v_reuseFailAlloc_2095_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2094_;
            }
            4 => {
                if v_isShared_2100_ == 0 {
                    v___x_2102_ = v___x_2099_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
                    v___x_2102_ = v_reuseFailAlloc_2103_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2102_;
            }
            6 => {
                if v_isShared_2112_ == 0 {
                    v___x_2114_ = v___x_2111_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
                    v___x_2114_ = v_reuseFailAlloc_2115_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1___boxed(
    mut v_i_2117_: *mut crate::leanh::LeanObject,
    mut v_as_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
    mut v___y_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2125_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v_i_2117_, v_as_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
    crate::leanh::lean_dec(v___y_2123_);
    crate::leanh::lean_dec_ref(v___y_2122_);
    crate::leanh::lean_dec(v___y_2121_);
    crate::leanh::lean_dec_ref(v___y_2120_);
    crate::leanh::lean_dec(v___y_2119_);
    return v_res_2125_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_addToPull___boxed(
    mut v_isFun_2126_: *mut crate::leanh::LeanObject,
    mut v_decl_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
    mut v_a_2129_: *mut crate::leanh::LeanObject,
    mut v_a_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
    mut v_a_2133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isFun_boxed_2134_: u8 = 0;
    let mut v_res_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isFun_boxed_2134_ = (crate::leanh::lean_unbox(v_isFun_2126_) as u8);
    v_res_2135_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(
        v_isFun_boxed_2134_,
        v_decl_2127_,
        v_a_2128_,
        v_a_2129_,
        v_a_2130_,
        v_a_2131_,
        v_a_2132_,
    );
    crate::leanh::lean_dec(v_a_2132_);
    crate::leanh::lean_dec_ref(v_a_2131_);
    crate::leanh::lean_dec(v_a_2130_);
    crate::leanh::lean_dec_ref(v_a_2129_);
    crate::leanh::lean_dec(v_a_2128_);
    return v_res_2135_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed(
    mut v_code_2136_: *mut crate::leanh::LeanObject,
    mut v_a_2137_: *mut crate::leanh::LeanObject,
    mut v_a_2138_: *mut crate::leanh::LeanObject,
    mut v_a_2139_: *mut crate::leanh::LeanObject,
    mut v_a_2140_: *mut crate::leanh::LeanObject,
    mut v_a_2141_: *mut crate::leanh::LeanObject,
    mut v_a_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
        v_code_2136_,
        v_a_2137_,
        v_a_2138_,
        v_a_2139_,
        v_a_2140_,
        v_a_2141_,
    );
    crate::leanh::lean_dec(v_a_2141_);
    crate::leanh::lean_dec_ref(v_a_2140_);
    crate::leanh::lean_dec(v_a_2139_);
    crate::leanh::lean_dec_ref(v_a_2138_);
    crate::leanh::lean_dec(v_a_2137_);
    return v_res_2143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(
    mut v_f_2144_: *mut crate::leanh::LeanObject,
    mut v_v_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2160_: u8 = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_2145_) == 0 {
                    v_code_2152_ = crate::leanh::lean_ctor_get(v_v_2145_, 0);
                    v_isSharedCheck_2176_ = (!crate::leanh::lean_is_exclusive(v_v_2145_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v___x_2154_ = v_v_2145_;
                        v_isShared_2155_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_2152_);
                        crate::leanh::lean_dec(v_v_2145_);
                        v___x_2154_ = crate::leanh::lean_box(0);
                        v_isShared_2155_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2144_);
                    v___x_2177_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2177_, 0, v_v_2145_);
                    return v___x_2177_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_2150_);
                crate::leanh::lean_inc_ref(v___y_2149_);
                crate::leanh::lean_inc(v___y_2148_);
                crate::leanh::lean_inc_ref(v___y_2147_);
                crate::leanh::lean_inc(v___y_2146_);
                v___x_2156_ = crate::leanh::lean_apply_7(
                    v_f_2144_,
                    v_code_2152_,
                    v___y_2146_,
                    v___y_2147_,
                    v___y_2148_,
                    v___y_2149_,
                    v___y_2150_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2156_) == 0 {
                    v_a_2157_ = crate::leanh::lean_ctor_get(v___x_2156_, 0);
                    v_isSharedCheck_2167_ = (!crate::leanh::lean_is_exclusive(v___x_2156_)) as u8;
                    if v_isSharedCheck_2167_ == 0 {
                        v___x_2159_ = v___x_2156_;
                        v_isShared_2160_ = v_isSharedCheck_2167_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2157_);
                        crate::leanh::lean_dec(v___x_2156_);
                        v___x_2159_ = crate::leanh::lean_box(0);
                        v_isShared_2160_ = v_isSharedCheck_2167_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2154_);
                    v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2156_, 0);
                    v_isSharedCheck_2175_ = (!crate::leanh::lean_is_exclusive(v___x_2156_)) as u8;
                    if v_isSharedCheck_2175_ == 0 {
                        v___x_2170_ = v___x_2156_;
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2168_);
                        crate::leanh::lean_dec(v___x_2156_);
                        v___x_2170_ = crate::leanh::lean_box(0);
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2154_, 0, v_a_2157_);
                    v___x_2162_ = v___x_2154_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2157_);
                    v___x_2162_ = v_reuseFailAlloc_2166_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2160_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2159_, 0, v___x_2162_);
                    v___x_2164_ = v___x_2159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
                    v___x_2164_ = v_reuseFailAlloc_2165_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2164_;
            }
            5 => {
                if v_isShared_2171_ == 0 {
                    v___x_2173_ = v___x_2170_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg___boxed(
    mut v_f_2178_: *mut crate::leanh::LeanObject,
    mut v_v_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2186_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_2178_, v_v_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
    crate::leanh::lean_dec(v___y_2184_);
    crate::leanh::lean_dec_ref(v___y_2183_);
    crate::leanh::lean_dec(v___y_2182_);
    crate::leanh::lean_dec_ref(v___y_2181_);
    crate::leanh::lean_dec(v___y_2180_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(
    mut v_pu_2187_: u8,
    mut v_f_2188_: *mut crate::leanh::LeanObject,
    mut v_v_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_2188_, v_v_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
    return v___x_2196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___boxed(
    mut v_pu_2197_: *mut crate::leanh::LeanObject,
    mut v_f_2198_: *mut crate::leanh::LeanObject,
    mut v_v_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2206_: u8 = 0;
    let mut v_res_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2206_ = (crate::leanh::lean_unbox(v_pu_2197_) as u8);
    v_res_2207_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(v_pu_boxed_2206_, v_f_2198_, v_v_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
    crate::leanh::lean_dec(v___y_2204_);
    crate::leanh::lean_dec_ref(v___y_2203_);
    crate::leanh::lean_dec(v___y_2202_);
    crate::leanh::lean_dec_ref(v___y_2201_);
    crate::leanh::lean_dec(v___y_2200_);
    return v_res_2207_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullFunDecls(
    mut v_decl_2209_: *mut crate::leanh::LeanObject,
    mut v_a_2210_: *mut crate::leanh::LeanObject,
    mut v_a_2211_: *mut crate::leanh::LeanObject,
    mut v_a_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_2219_: u8 = 0;
    let mut v_inlineAttr_x3f_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_a_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2215_ = crate::leanh::lean_box(0);
                v___x_2216_ = lean_st_mk_ref(v___x_2215_);
                v_toSignature_2217_ = crate::leanh::lean_ctor_get(v_decl_2209_, 0);
                v_value_2218_ = crate::leanh::lean_ctor_get(v_decl_2209_, 1);
                v_recursive_2219_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_2209_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_2220_ = crate::leanh::lean_ctor_get(v_decl_2209_, 2);
                v_isSharedCheck_2249_ = (!crate::leanh::lean_is_exclusive(v_decl_2209_)) as u8;
                if v_isSharedCheck_2249_ == 0 {
                    v___x_2222_ = v_decl_2209_;
                    v_isShared_2223_ = v_isSharedCheck_2249_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_2220_);
                    crate::leanh::lean_inc(v_value_2218_);
                    crate::leanh::lean_inc(v_toSignature_2217_);
                    crate::leanh::lean_dec(v_decl_2209_);
                    v___x_2222_ = crate::leanh::lean_box(0);
                    v_isShared_2223_ = v_isSharedCheck_2249_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2224_ = l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0;
                v___x_2225_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v___x_2224_, v_value_2218_, v___x_2216_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
                if crate::leanh::lean_obj_tag(v___x_2225_) == 0 {
                    v_a_2226_ = crate::leanh::lean_ctor_get(v___x_2225_, 0);
                    v_isSharedCheck_2240_ = (!crate::leanh::lean_is_exclusive(v___x_2225_)) as u8;
                    if v_isSharedCheck_2240_ == 0 {
                        v___x_2228_ = v___x_2225_;
                        v_isShared_2229_ = v_isSharedCheck_2240_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2226_);
                        crate::leanh::lean_dec(v___x_2225_);
                        v___x_2228_ = crate::leanh::lean_box(0);
                        v_isShared_2229_ = v_isSharedCheck_2240_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2222_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_2220_);
                    crate::leanh::lean_dec_ref(v_toSignature_2217_);
                    crate::leanh::lean_dec(v___x_2216_);
                    v_a_2241_ = crate::leanh::lean_ctor_get(v___x_2225_, 0);
                    v_isSharedCheck_2248_ = (!crate::leanh::lean_is_exclusive(v___x_2225_)) as u8;
                    if v_isSharedCheck_2248_ == 0 {
                        v___x_2243_ = v___x_2225_;
                        v_isShared_2244_ = v_isSharedCheck_2248_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2241_);
                        crate::leanh::lean_dec(v___x_2225_);
                        v___x_2243_ = crate::leanh::lean_box(0);
                        v_isShared_2244_ = v_isSharedCheck_2248_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2230_ = lean_st_ref_get(v___x_2216_);
                crate::leanh::lean_dec(v___x_2216_);
                v___x_2231_ = lean_array_mk(v___x_2230_);
                v___x_2232_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_PullFunDecls_attach as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_2232_, 0, v___x_2231_);
                v___x_2233_ =
                    l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(v___x_2232_, v_a_2226_);
                if v_isShared_2223_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2222_, 1, v___x_2233_);
                    v___x_2235_ = v___x_2222_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_toSignature_2217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_inlineAttr_x3f_2220_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2239_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_2219_,
                    );
                    v___x_2235_ = v_reuseFailAlloc_2239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2235_);
                    v___x_2237_ = v___x_2228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
                    v___x_2237_ = v_reuseFailAlloc_2238_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2237_;
            }
            5 => {
                if v_isShared_2244_ == 0 {
                    v___x_2246_ = v___x_2243_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
                    v___x_2246_ = v_reuseFailAlloc_2247_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullFunDecls___boxed(
    mut v_decl_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
    mut v_a_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_Compiler_LCNF_Decl_pullFunDecls(
        v_decl_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
    );
    crate::leanh::lean_dec(v_a_2254_);
    crate::leanh::lean_dec_ref(v_a_2253_);
    crate::leanh::lean_dec(v_a_2252_);
    crate::leanh::lean_dec_ref(v_a_2251_);
    return v_res_2256_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2262_ = l_Lean_Compiler_LCNF_pullFunDecls___closed__2;
    v___x_2263_ = 0;
    v___x_2264_ = l_Lean_Compiler_LCNF_pullFunDecls___closed__1;
    v___x_2265_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_2264_,
        v___x_2263_,
        v___x_2262_,
        v___x_2261_,
    );
    return v___x_2265_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_pullFunDecls() -> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_pullFunDecls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_pullFunDecls___closed__3_once),
        _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3,
    );
    return v___x_2266_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_;
    v___x_2338_ = 1;
    v___x_2339_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_;
    v___x_2340_ = l_Lean_registerTraceClass(v___x_2337_, v___x_2338_, v___x_2339_);
    return v___x_2340_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2____boxed(
    mut v_a_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2342_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
    return v_res_2342_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default =
        _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default,
    );
    l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull =
        _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull);
    l_Lean_Compiler_LCNF_pullFunDecls = _init_l_Lean_Compiler_LCNF_pullFunDecls();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls);
    res = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PullFunDecls(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_PullFunDecls(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
}
