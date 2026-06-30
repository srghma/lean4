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
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullFunDecls___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value)
                as *mut leanh::LeanObject,
            15479406399762191914 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullFunDecls___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_Decl_pullFunDecls___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_pullFunDecls___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_pullFunDecls: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value) as *mut leanh::LeanObject,7687188514397653396 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1501781890156459336 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4203849195465939425 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 117, 108, 108, 70, 117, 110, 68, 101, 99, 108, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4715093308645774882 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,8361423566811915395 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9903248596004213070 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,424871438967119852 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10437388805546877613 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,491910158757896708 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8630099969334220429 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,668284432093445752 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16269612643220945362 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6062304044350350739 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12890017594083057032 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1553090079 as usize) << 1) | 1) as *mut leanh::LeanObject,11458291349318782630 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5573388920595387873 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11256589942589999705 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,8502987044875405700 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = 0;
    v___x_1173_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(v___x_1172_);
    return v___x_1173_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_instInhabitedFVarIdHashSet;
    v___x_1175_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0,
    );
    v___x_1176_ = 0;
    v___x_1177_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_1177_, 0, v___x_1175_);
    leanh::lean_ctor_set(v___x_1177_, 1, v___x_1174_);
    leanh::lean_ctor_set_uint8(
        v___x_1177_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_1176_,
    );
    return v___x_1177_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default()
-> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
    return v___x_1179_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(
    mut v_a_1180_: *mut leanh::LeanObject,
    mut v_x_1181_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1182_: u8 = 0;
    let mut v_key_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1181_) == 0 {
                    v___x_1182_ = 0;
                    return v___x_1182_;
                } else {
                    v_key_1183_ = leanh::lean_ctor_get(v_x_1181_, 0);
                    v_tail_1184_ = leanh::lean_ctor_get(v_x_1181_, 2);
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
    mut v_a_1187_: *mut leanh::LeanObject,
    mut v_x_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1189_: u8 = 0;
    let mut v_r_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_1187_, v_x_1188_);
    leanh::lean_dec(v_x_1188_);
    leanh::lean_dec(v_a_1187_);
    v_r_1190_ = leanh::lean_box((v_res_1189_) as usize);
    return v_r_1190_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(
    mut v_m_1191_: *mut leanh::LeanObject,
    mut v_a_1192_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: u8 = 0;
    v_buckets_1193_ = leanh::lean_ctor_get(v_m_1191_, 1);
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
    mut v_m_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1211_: u8 = 0;
    let mut v_r_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_1209_, v_a_1210_);
    leanh::lean_dec(v_a_1210_);
    leanh::lean_dec_ref(v_m_1209_);
    v_r_1212_ = leanh::lean_box((v_res_1211_) as usize);
    return v_r_1212_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(
    mut v_fvarId_1213_: *mut leanh::LeanObject,
    mut v_as_1214_: *mut leanh::LeanObject,
    mut v_keep_1215_: *mut leanh::LeanObject,
    mut v_dep_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v_used_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: u8 = 0;
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_1214_) == 0 {
                    v___x_1218_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1218_, 0, v_keep_1215_);
                    leanh::lean_ctor_set(v___x_1218_, 1, v_dep_1216_);
                    v___x_1219_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1219_, 0, v___x_1218_);
                    return v___x_1219_;
                } else {
                    v_head_1220_ = leanh::lean_ctor_get(v_as_1214_, 0);
                    v_tail_1221_ = leanh::lean_ctor_get(v_as_1214_, 1);
                    v_isSharedCheck_1235_ = (!leanh::lean_is_exclusive(v_as_1214_)) as u8;
                    if v_isSharedCheck_1235_ == 0 {
                        v___x_1223_ = v_as_1214_;
                        v_isShared_1224_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1221_);
                        leanh::lean_inc(v_head_1220_);
                        leanh::lean_dec(v_as_1214_);
                        v___x_1223_ = leanh::lean_box(0);
                        v_isShared_1224_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_used_1225_ = leanh::lean_ctor_get(v_head_1220_, 1);
                v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_1225_, v_fvarId_1213_);
                if v___x_1226_ == 0 {
                    if v_isShared_1224_ == 0 {
                        leanh::lean_ctor_set(v___x_1223_, 1, v_keep_1215_);
                        v___x_1228_ = v___x_1223_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1230_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_head_1220_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_keep_1215_);
                        v___x_1228_ = v_reuseFailAlloc_1230_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1224_ == 0 {
                        leanh::lean_ctor_set(v___x_1223_, 1, v_dep_1216_);
                        v___x_1232_ = v___x_1223_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1234_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_head_1220_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_dep_1216_);
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
    mut v_fvarId_1236_: *mut leanh::LeanObject,
    mut v_as_1237_: *mut leanh::LeanObject,
    mut v_keep_1238_: *mut leanh::LeanObject,
    mut v_dep_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1241_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_1236_, v_as_1237_, v_keep_1238_, v_dep_1239_);
    leanh::lean_dec(v_fvarId_1236_);
    return v_res_1241_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(
    mut v_fvarId_1242_: *mut leanh::LeanObject,
    mut v_as_1243_: *mut leanh::LeanObject,
    mut v_keep_1244_: *mut leanh::LeanObject,
    mut v_dep_1245_: *mut leanh::LeanObject,
    mut v_a_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_1242_, v_as_1243_, v_keep_1244_, v_dep_1245_);
    return v___x_1249_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___boxed(
    mut v_fvarId_1250_: *mut leanh::LeanObject,
    mut v_as_1251_: *mut leanh::LeanObject,
    mut v_keep_1252_: *mut leanh::LeanObject,
    mut v_dep_1253_: *mut leanh::LeanObject,
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v_a_1255_: *mut leanh::LeanObject,
    mut v_a_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1257_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(v_fvarId_1250_, v_as_1251_, v_keep_1252_, v_dep_1253_, v_a_1254_, v_a_1255_);
    leanh::lean_dec(v_a_1255_);
    leanh::lean_dec_ref(v_a_1254_);
    leanh::lean_dec(v_fvarId_1250_);
    return v_res_1257_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(
    mut v_00_u03b2_1258_: *mut leanh::LeanObject,
    mut v_m_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1261_: u8 = 0;
    v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_1259_, v_a_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___boxed(
    mut v_00_u03b2_1262_: *mut leanh::LeanObject,
    mut v_m_1263_: *mut leanh::LeanObject,
    mut v_a_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1265_: u8 = 0;
    let mut v_r_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(v_00_u03b2_1262_, v_m_1263_, v_a_1264_);
    leanh::lean_dec(v_a_1264_);
    leanh::lean_dec_ref(v_m_1263_);
    v_r_1266_ = leanh::lean_box((v_res_1265_) as usize);
    return v_r_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(
    mut v_00_u03b2_1267_: *mut leanh::LeanObject,
    mut v_a_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1270_: u8 = 0;
    v___x_1270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_1268_, v_x_1269_);
    return v___x_1270_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1271_: *mut leanh::LeanObject,
    mut v_a_1272_: *mut leanh::LeanObject,
    mut v_x_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1274_: u8 = 0;
    let mut v_r_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(v_00_u03b2_1271_, v_a_1272_, v_x_1273_);
    leanh::lean_dec(v_x_1273_);
    leanh::lean_dec(v_a_1272_);
    v_r_1275_ = leanh::lean_box((v_res_1274_) as usize);
    return v_r_1275_;
}
pub unsafe fn l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(
    mut v_fvarId_1276_: *mut leanh::LeanObject,
    mut v_x_1277_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1278_: u8 = 0;
    let mut v_head_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1277_) == 0 {
                    v___x_1278_ = 0;
                    return v___x_1278_;
                } else {
                    v_head_1279_ = leanh::lean_ctor_get(v_x_1277_, 0);
                    v_tail_1280_ = leanh::lean_ctor_get(v_x_1277_, 1);
                    v_used_1281_ = leanh::lean_ctor_get(v_head_1279_, 1);
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
    mut v_fvarId_1284_: *mut leanh::LeanObject,
    mut v_x_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1286_: u8 = 0;
    let mut v_r_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1286_ = l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(
        v_fvarId_1284_,
        v_x_1285_,
    );
    leanh::lean_dec(v_x_1285_);
    leanh::lean_dec(v_fvarId_1284_);
    v_r_1287_ = leanh::lean_box((v_res_1286_) as usize);
    return v_r_1287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(
    mut v_fvarId_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v_fst_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec(v___x_1291_);
                    v___x_1293_ = leanh::lean_box(0);
                    v___x_1294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1294_, 0, v___x_1293_);
                    return v___x_1294_;
                } else {
                    v___x_1295_ = leanh::lean_box(0);
                    v___x_1296_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_1288_, v___x_1291_, v___x_1295_, v___x_1295_);
                    v_a_1297_ = leanh::lean_ctor_get(v___x_1296_, 0);
                    v_isSharedCheck_1307_ = (!leanh::lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1299_ = v___x_1296_;
                        v_isShared_1300_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1297_);
                        leanh::lean_dec(v___x_1296_);
                        v___x_1299_ = leanh::lean_box(0);
                        v_isShared_1300_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1301_ = leanh::lean_ctor_get(v_a_1297_, 0);
                leanh::lean_inc(v_fst_1301_);
                v_snd_1302_ = leanh::lean_ctor_get(v_a_1297_, 1);
                leanh::lean_inc(v_snd_1302_);
                leanh::lean_dec(v_a_1297_);
                v___x_1303_ = lean_st_ref_set(v_a_1289_, v_fst_1301_);
                if v_isShared_1300_ == 0 {
                    leanh::lean_ctor_set(v___x_1299_, 0, v_snd_1302_);
                    v___x_1305_ = v___x_1299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_snd_1302_);
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
    mut v_fvarId_1308_: *mut leanh::LeanObject,
    mut v_a_1309_: *mut leanh::LeanObject,
    mut v_a_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_1308_, v_a_1309_);
    leanh::lean_dec(v_a_1309_);
    leanh::lean_dec(v_fvarId_1308_);
    return v_res_1311_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(
    mut v_fvarId_1312_: *mut leanh::LeanObject,
    mut v_a_1313_: *mut leanh::LeanObject,
    mut v_a_1314_: *mut leanh::LeanObject,
    mut v_a_1315_: *mut leanh::LeanObject,
    mut v_a_1316_: *mut leanh::LeanObject,
    mut v_a_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_1312_, v_a_1313_);
    return v___x_1319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___boxed(
    mut v_fvarId_1320_: *mut leanh::LeanObject,
    mut v_a_1321_: *mut leanh::LeanObject,
    mut v_a_1322_: *mut leanh::LeanObject,
    mut v_a_1323_: *mut leanh::LeanObject,
    mut v_a_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(
        v_fvarId_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
        v_a_1324_,
        v_a_1325_,
    );
    leanh::lean_dec(v_a_1325_);
    leanh::lean_dec_ref(v_a_1324_);
    leanh::lean_dec(v_a_1323_);
    leanh::lean_dec_ref(v_a_1322_);
    leanh::lean_dec(v_a_1321_);
    leanh::lean_dec(v_fvarId_1320_);
    return v_res_1327_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
    mut v_todo_1328_: *mut leanh::LeanObject,
    mut v_acc_1329_: *mut leanh::LeanObject,
    mut v_a_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_todo_1328_) == 0 {
                    v___x_1332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1332_, 0, v_acc_1329_);
                    return v___x_1332_;
                } else {
                    v_head_1333_ = leanh::lean_ctor_get(v_todo_1328_, 0);
                    leanh::lean_inc(v_head_1333_);
                    v_decl_1334_ = leanh::lean_ctor_get(v_head_1333_, 0);
                    v_tail_1335_ = leanh::lean_ctor_get(v_todo_1328_, 1);
                    leanh::lean_inc(v_tail_1335_);
                    leanh::lean_dec_ref_known(v_todo_1328_, 2);
                    v_fvarId_1336_ = leanh::lean_ctor_get(v_decl_1334_, 0);
                    v___x_1337_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(
                        v_fvarId_1336_,
                        v_a_1330_,
                    );
                    if leanh::lean_obj_tag(v___x_1337_) == 0 {
                        v_a_1338_ = leanh::lean_ctor_get(v___x_1337_, 0);
                        leanh::lean_inc(v_a_1338_);
                        leanh::lean_dec_ref_known(v___x_1337_, 1);
                        v___x_1339_ = l_List_appendTR___redArg(v_a_1338_, v_tail_1335_);
                        v___x_1340_ = lean_array_push(v_acc_1329_, v_head_1333_);
                        v_todo_1328_ = v___x_1339_;
                        v_acc_1329_ = v___x_1340_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1335_);
                        leanh::lean_dec(v_head_1333_);
                        leanh::lean_dec_ref(v_acc_1329_);
                        v_a_1342_ = leanh::lean_ctor_get(v___x_1337_, 0);
                        v_isSharedCheck_1349_ =
                            (!leanh::lean_is_exclusive(v___x_1337_)) as u8;
                        if v_isSharedCheck_1349_ == 0 {
                            v___x_1344_ = v___x_1337_;
                            v_isShared_1345_ = v_isSharedCheck_1349_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1342_);
                            leanh::lean_dec(v___x_1337_);
                            v___x_1344_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1348_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
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
    mut v_todo_1350_: *mut leanh::LeanObject,
    mut v_acc_1351_: *mut leanh::LeanObject,
    mut v_a_1352_: *mut leanh::LeanObject,
    mut v_a_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
        v_todo_1350_,
        v_acc_1351_,
        v_a_1352_,
    );
    leanh::lean_dec(v_a_1352_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(
    mut v_todo_1355_: *mut leanh::LeanObject,
    mut v_acc_1356_: *mut leanh::LeanObject,
    mut v_a_1357_: *mut leanh::LeanObject,
    mut v_a_1358_: *mut leanh::LeanObject,
    mut v_a_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
    mut v_a_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
        v_todo_1355_,
        v_acc_1356_,
        v_a_1357_,
    );
    return v___x_1363_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___boxed(
    mut v_todo_1364_: *mut leanh::LeanObject,
    mut v_acc_1365_: *mut leanh::LeanObject,
    mut v_a_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_a_1368_: *mut leanh::LeanObject,
    mut v_a_1369_: *mut leanh::LeanObject,
    mut v_a_1370_: *mut leanh::LeanObject,
    mut v_a_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(
        v_todo_1364_,
        v_acc_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
        v_a_1370_,
    );
    leanh::lean_dec(v_a_1370_);
    leanh::lean_dec_ref(v_a_1369_);
    leanh::lean_dec(v_a_1368_);
    leanh::lean_dec_ref(v_a_1367_);
    leanh::lean_dec(v_a_1366_);
    return v_res_1372_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(
    mut v_fvarId_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1378_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(
                    v_fvarId_1375_,
                    v_a_1376_,
                );
                if leanh::lean_obj_tag(v___x_1378_) == 0 {
                    v_a_1379_ = leanh::lean_ctor_get(v___x_1378_, 0);
                    leanh::lean_inc(v_a_1379_);
                    leanh::lean_dec_ref_known(v___x_1378_, 1);
                    v___x_1380_ =
                        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0;
                    v___x_1381_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(
                        v_a_1379_,
                        v___x_1380_,
                        v_a_1376_,
                    );
                    return v___x_1381_;
                } else {
                    v_a_1382_ = leanh::lean_ctor_get(v___x_1378_, 0);
                    v_isSharedCheck_1389_ = (!leanh::lean_is_exclusive(v___x_1378_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1384_ = v___x_1378_;
                        v_isShared_1385_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1382_);
                        leanh::lean_dec(v___x_1378_);
                        v___x_1384_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1388_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
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
    mut v_fvarId_1390_: *mut leanh::LeanObject,
    mut v_a_1391_: *mut leanh::LeanObject,
    mut v_a_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_1390_, v_a_1391_);
    leanh::lean_dec(v_a_1391_);
    leanh::lean_dec(v_fvarId_1390_);
    return v_res_1393_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(
    mut v_fvarId_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ =
        l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_1394_, v_a_1395_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___boxed(
    mut v_fvarId_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_a_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
    mut v_a_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1409_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(
        v_fvarId_1402_,
        v_a_1403_,
        v_a_1404_,
        v_a_1405_,
        v_a_1406_,
        v_a_1407_,
    );
    leanh::lean_dec(v_a_1407_);
    leanh::lean_dec_ref(v_a_1406_);
    leanh::lean_dec(v_a_1405_);
    leanh::lean_dec_ref(v_a_1404_);
    leanh::lean_dec(v_a_1403_);
    leanh::lean_dec(v_fvarId_1402_);
    return v_res_1409_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(
    mut v_as_1410_: *mut leanh::LeanObject,
    mut v_sz_1411_: usize,
    mut v_i_1412_: usize,
    mut v_b_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: u8 = 0;
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: usize = 0;
    let mut v___x_1424_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1416_ = lean_usize_dec_lt(v_i_1412_, v_sz_1411_);
                if v___x_1416_ == 0 {
                    v___x_1417_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1417_, 0, v_b_1413_);
                    return v___x_1417_;
                } else {
                    v_a_1418_ = lean_array_uget_borrowed(v_as_1410_, v_i_1412_);
                    v_fvarId_1419_ = leanh::lean_ctor_get(v_a_1418_, 0);
                    v___x_1420_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(
                        v_fvarId_1419_,
                        v___y_1414_,
                    );
                    if leanh::lean_obj_tag(v___x_1420_) == 0 {
                        v_a_1421_ = leanh::lean_ctor_get(v___x_1420_, 0);
                        leanh::lean_inc(v_a_1421_);
                        leanh::lean_dec_ref_known(v___x_1420_, 1);
                        v___x_1422_ = l_Array_append___redArg(v_b_1413_, v_a_1421_);
                        leanh::lean_dec(v_a_1421_);
                        v___x_1423_ = 1usize;
                        v___x_1424_ = lean_usize_add(v_i_1412_, v___x_1423_);
                        v_i_1412_ = v___x_1424_;
                        v_b_1413_ = v___x_1422_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_1413_);
                        return v___x_1420_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg___boxed(
    mut v_as_1426_: *mut leanh::LeanObject,
    mut v_sz_1427_: *mut leanh::LeanObject,
    mut v_i_1428_: *mut leanh::LeanObject,
    mut v_b_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1432_: usize = 0;
    let mut v_i_boxed_1433_: usize = 0;
    let mut v_res_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1432_ = leanh::lean_unbox_usize(v_sz_1427_);
    leanh::lean_dec(v_sz_1427_);
    v_i_boxed_1433_ = leanh::lean_unbox_usize(v_i_1428_);
    leanh::lean_dec(v_i_1428_);
    v_res_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_1426_, v_sz_boxed_1432_, v_i_boxed_1433_, v_b_1429_, v___y_1430_);
    leanh::lean_dec(v___y_1430_);
    leanh::lean_dec_ref(v_as_1426_);
    return v_res_1434_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(
    mut v_params_1435_: *mut leanh::LeanObject,
    mut v_a_1436_: *mut leanh::LeanObject,
    mut v_a_1437_: *mut leanh::LeanObject,
    mut v_a_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_acc_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1443_: usize = 0;
    let mut v___x_1444_: usize = 0;
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_acc_1442_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0;
    v_sz_1443_ = lean_array_size(v_params_1435_);
    v___x_1444_ = 0usize;
    v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_params_1435_, v_sz_1443_, v___x_1444_, v_acc_1442_, v_a_1436_);
    return v___x_1445_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg___boxed(
    mut v_params_1446_: *mut leanh::LeanObject,
    mut v_a_1447_: *mut leanh::LeanObject,
    mut v_a_1448_: *mut leanh::LeanObject,
    mut v_a_1449_: *mut leanh::LeanObject,
    mut v_a_1450_: *mut leanh::LeanObject,
    mut v_a_1451_: *mut leanh::LeanObject,
    mut v_a_1452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(
        v_params_1446_,
        v_a_1447_,
        v_a_1448_,
        v_a_1449_,
        v_a_1450_,
        v_a_1451_,
    );
    leanh::lean_dec(v_a_1451_);
    leanh::lean_dec_ref(v_a_1450_);
    leanh::lean_dec(v_a_1449_);
    leanh::lean_dec_ref(v_a_1448_);
    leanh::lean_dec(v_a_1447_);
    leanh::lean_dec_ref(v_params_1446_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(
    mut v_pu_1454_: u8,
    mut v_params_1455_: *mut leanh::LeanObject,
    mut v_a_1456_: *mut leanh::LeanObject,
    mut v_a_1457_: *mut leanh::LeanObject,
    mut v_a_1458_: *mut leanh::LeanObject,
    mut v_a_1459_: *mut leanh::LeanObject,
    mut v_a_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_pu_1463_: *mut leanh::LeanObject,
    mut v_params_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v_a_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1471_: u8 = 0;
    let mut v_res_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1471_ = (leanh::lean_unbox(v_pu_1463_) as u8);
    v_res_1472_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(
        v_pu_boxed_1471_,
        v_params_1464_,
        v_a_1465_,
        v_a_1466_,
        v_a_1467_,
        v_a_1468_,
        v_a_1469_,
    );
    leanh::lean_dec(v_a_1469_);
    leanh::lean_dec_ref(v_a_1468_);
    leanh::lean_dec(v_a_1467_);
    leanh::lean_dec_ref(v_a_1466_);
    leanh::lean_dec(v_a_1465_);
    leanh::lean_dec_ref(v_params_1464_);
    return v_res_1472_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(
    mut v_as_1473_: *mut leanh::LeanObject,
    mut v_sz_1474_: usize,
    mut v_i_1475_: usize,
    mut v_b_1476_: *mut leanh::LeanObject,
    mut v___y_1477_: *mut leanh::LeanObject,
    mut v___y_1478_: *mut leanh::LeanObject,
    mut v___y_1479_: *mut leanh::LeanObject,
    mut v___y_1480_: *mut leanh::LeanObject,
    mut v___y_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_1473_, v_sz_1474_, v_i_1475_, v_b_1476_, v___y_1477_);
    return v___x_1483_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___boxed(
    mut v_as_1484_: *mut leanh::LeanObject,
    mut v_sz_1485_: *mut leanh::LeanObject,
    mut v_i_1486_: *mut leanh::LeanObject,
    mut v_b_1487_: *mut leanh::LeanObject,
    mut v___y_1488_: *mut leanh::LeanObject,
    mut v___y_1489_: *mut leanh::LeanObject,
    mut v___y_1490_: *mut leanh::LeanObject,
    mut v___y_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1494_: usize = 0;
    let mut v_i_boxed_1495_: usize = 0;
    let mut v_res_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1494_ = leanh::lean_unbox_usize(v_sz_1485_);
    leanh::lean_dec(v_sz_1485_);
    v_i_boxed_1495_ = leanh::lean_unbox_usize(v_i_1486_);
    leanh::lean_dec(v_i_1486_);
    v_res_1496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(v_as_1484_, v_sz_boxed_1494_, v_i_boxed_1495_, v_b_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
    leanh::lean_dec(v___y_1492_);
    leanh::lean_dec_ref(v___y_1491_);
    leanh::lean_dec(v___y_1490_);
    leanh::lean_dec_ref(v___y_1489_);
    leanh::lean_dec(v___y_1488_);
    leanh::lean_dec_ref(v_as_1484_);
    return v_res_1496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(
    mut v_p_1497_: *mut leanh::LeanObject,
    mut v_k_1498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isFun_1499_: u8 = 0;
    v_isFun_1499_ = leanh::lean_ctor_get_uint8(
        v_p_1497_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_isFun_1499_ == 0 {
        let mut v_decl_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_decl_1500_ = leanh::lean_ctor_get(v_p_1497_, 0);
        leanh::lean_inc_ref(v_decl_1500_);
        v___x_1501_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1501_, 0, v_decl_1500_);
        leanh::lean_ctor_set(v___x_1501_, 1, v_k_1498_);
        return v___x_1501_;
    } else {
        let mut v_decl_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_decl_1502_ = leanh::lean_ctor_get(v_p_1497_, 0);
        leanh::lean_inc_ref(v_decl_1502_);
        v___x_1503_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1503_, 0, v_decl_1502_);
        leanh::lean_ctor_set(v___x_1503_, 1, v_k_1498_);
        return v___x_1503_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach___boxed(
    mut v_p_1504_: *mut leanh::LeanObject,
    mut v_k_1505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1506_ = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v_p_1504_, v_k_1505_);
    leanh::lean_dec_ref(v_p_1504_);
    return v_res_1506_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(
    mut v_i_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_1509_ = leanh::lean_ctor_get(v_a_1508_, 1);
    v___x_1510_ = 0;
    v___x_1511_ = leanh::lean_box((v___x_1510_) as usize);
    v___x_1512_ = lean_array_get(v___x_1511_, v_snd_1509_, v_i_1507_);
    leanh::lean_dec(v___x_1511_);
    v___x_1513_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    leanh::lean_ctor_set(v___x_1513_, 1, v_a_1508_);
    return v___x_1513_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited___boxed(
    mut v_i_1514_: *mut leanh::LeanObject,
    mut v_a_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1516_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_1514_, v_a_1515_);
    leanh::lean_dec(v_i_1514_);
    return v_res_1516_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(
    mut v_upperBound_1517_: *mut leanh::LeanObject,
    mut v___x_1518_: *mut leanh::LeanObject,
    mut v_ps_1519_: *mut leanh::LeanObject,
    mut v_a_1520_: *mut leanh::LeanObject,
    mut v_b_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v_decl_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1529_ = lean_nat_dec_lt(v_a_1520_, v_upperBound_1517_);
                if v___x_1529_ == 0 {
                    leanh::lean_dec(v_a_1520_);
                    v___x_1530_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1530_, 0, v_b_1521_);
                    leanh::lean_ctor_set(v___x_1530_, 1, v___y_1522_);
                    return v___x_1530_;
                } else {
                    v___x_1531_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_a_1520_, v___y_1522_);
                    v_fst_1532_ = leanh::lean_ctor_get(v___x_1531_, 0);
                    leanh::lean_inc(v_fst_1532_);
                    v_snd_1533_ = leanh::lean_ctor_get(v___x_1531_, 1);
                    leanh::lean_inc(v_snd_1533_);
                    leanh::lean_dec_ref(v___x_1531_);
                    v___x_1534_ = leanh::lean_box(0);
                    v___x_1535_ = (leanh::lean_unbox(v_fst_1532_) as u8);
                    leanh::lean_dec(v_fst_1532_);
                    if v___x_1535_ == 0 {
                        v_decl_1536_ = leanh::lean_ctor_get(v___x_1518_, 0);
                        v_fvarId_1537_ = leanh::lean_ctor_get(v_decl_1536_, 0);
                        v___x_1538_ = lean_array_fget_borrowed(v_ps_1519_, v_a_1520_);
                        v_used_1539_ = leanh::lean_ctor_get(v___x_1538_, 1);
                        v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_1539_, v_fvarId_1537_);
                        if v___x_1540_ == 0 {
                            v_a_1524_ = v___x_1534_;
                            v_snd_1525_ = v_snd_1533_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1541_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_1519_, v_a_1520_, v_snd_1533_);
                            v_snd_1542_ = leanh::lean_ctor_get(v___x_1541_, 1);
                            leanh::lean_inc(v_snd_1542_);
                            leanh::lean_dec_ref(v___x_1541_);
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
                v___x_1526_ = leanh::lean_unsigned_to_nat(1);
                v___x_1527_ = lean_nat_add(v_a_1520_, v___x_1526_);
                leanh::lean_dec(v_a_1520_);
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
    mut v_ps_1543_: *mut leanh::LeanObject,
    mut v_i_1544_: *mut leanh::LeanObject,
    mut v_a_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v_snd_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v_fst_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_isSharedCheck_1583_: u8 = 0;
    let mut v_unused_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut v_snd_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_unused_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1546_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_1544_, v_a_1545_);
                v_fst_1547_ = leanh::lean_ctor_get(v___x_1546_, 0);
                leanh::lean_inc(v_fst_1547_);
                v___x_1548_ = (leanh::lean_unbox(v_fst_1547_) as u8);
                leanh::lean_dec(v_fst_1547_);
                if v___x_1548_ == 0 {
                    v_snd_1549_ = leanh::lean_ctor_get(v___x_1546_, 1);
                    leanh::lean_inc(v_snd_1549_);
                    leanh::lean_dec_ref(v___x_1546_);
                    v_fst_1550_ = leanh::lean_ctor_get(v_snd_1549_, 0);
                    v_snd_1551_ = leanh::lean_ctor_get(v_snd_1549_, 1);
                    v_isSharedCheck_1586_ = (!leanh::lean_is_exclusive(v_snd_1549_)) as u8;
                    if v_isSharedCheck_1586_ == 0 {
                        v___x_1553_ = v_snd_1549_;
                        v_isShared_1554_ = v_isSharedCheck_1586_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1551_);
                        leanh::lean_inc(v_fst_1550_);
                        leanh::lean_dec(v_snd_1549_);
                        v___x_1553_ = leanh::lean_box(0);
                        v_isShared_1554_ = v_isSharedCheck_1586_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_1587_ = leanh::lean_ctor_get(v___x_1546_, 1);
                    v_isSharedCheck_1595_ = (!leanh::lean_is_exclusive(v___x_1546_)) as u8;
                    if v_isSharedCheck_1595_ == 0 {
                        v_unused_1596_ = leanh::lean_ctor_get(v___x_1546_, 0);
                        leanh::lean_dec(v_unused_1596_);
                        v___x_1589_ = v___x_1546_;
                        v_isShared_1590_ = v_isSharedCheck_1595_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1587_);
                        leanh::lean_dec(v___x_1546_);
                        v___x_1589_ = leanh::lean_box(0);
                        v_isShared_1590_ = v_isSharedCheck_1595_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1555_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
                v___x_1556_ = lean_array_get_size(v_ps_1543_);
                v___x_1557_ = leanh::lean_unsigned_to_nat(0);
                v___x_1558_ = 1;
                v___x_1559_ = leanh::lean_box((v___x_1558_) as usize);
                v___x_1560_ = lean_array_set(v_snd_1551_, v_i_1544_, v___x_1559_);
                v___x_1561_ = lean_array_get_borrowed(v___x_1555_, v_ps_1543_, v_i_1544_);
                if v_isShared_1554_ == 0 {
                    leanh::lean_ctor_set(v___x_1553_, 1, v___x_1560_);
                    v___x_1563_ = v___x_1553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_fst_1550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1560_);
                    v___x_1563_ = v_reuseFailAlloc_1585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1564_ = leanh::lean_box(0);
                v___x_1565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v___x_1556_, v___x_1561_, v_ps_1543_, v___x_1557_, v___x_1564_, v___x_1563_);
                v_snd_1566_ = leanh::lean_ctor_get(v___x_1565_, 1);
                v_isSharedCheck_1583_ = (!leanh::lean_is_exclusive(v___x_1565_)) as u8;
                if v_isSharedCheck_1583_ == 0 {
                    v_unused_1584_ = leanh::lean_ctor_get(v___x_1565_, 0);
                    leanh::lean_dec(v_unused_1584_);
                    v___x_1568_ = v___x_1565_;
                    v_isShared_1569_ = v_isSharedCheck_1583_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1566_);
                    leanh::lean_dec(v___x_1565_);
                    v___x_1568_ = leanh::lean_box(0);
                    v_isShared_1569_ = v_isSharedCheck_1583_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_1570_ = leanh::lean_ctor_get(v_snd_1566_, 0);
                v_snd_1571_ = leanh::lean_ctor_get(v_snd_1566_, 1);
                v_isSharedCheck_1582_ = (!leanh::lean_is_exclusive(v_snd_1566_)) as u8;
                if v_isSharedCheck_1582_ == 0 {
                    v___x_1573_ = v_snd_1566_;
                    v_isShared_1574_ = v_isSharedCheck_1582_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1571_);
                    leanh::lean_inc(v_fst_1570_);
                    leanh::lean_dec(v_snd_1566_);
                    v___x_1573_ = leanh::lean_box(0);
                    v_isShared_1574_ = v_isSharedCheck_1582_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1575_ =
                    l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v___x_1561_, v_fst_1570_);
                if v_isShared_1574_ == 0 {
                    leanh::lean_ctor_set(v___x_1573_, 0, v___x_1575_);
                    v___x_1577_ = v___x_1573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_snd_1571_);
                    v___x_1577_ = v_reuseFailAlloc_1581_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1569_ == 0 {
                    leanh::lean_ctor_set(v___x_1568_, 1, v___x_1577_);
                    leanh::lean_ctor_set(v___x_1568_, 0, v___x_1564_);
                    v___x_1579_ = v___x_1568_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1564_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___x_1577_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1579_;
            }
            7 => {
                v___x_1591_ = leanh::lean_box(0);
                if v_isShared_1590_ == 0 {
                    leanh::lean_ctor_set(v___x_1589_, 0, v___x_1591_);
                    v___x_1593_ = v___x_1589_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_snd_1587_);
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
    mut v_ps_1597_: *mut leanh::LeanObject,
    mut v_i_1598_: *mut leanh::LeanObject,
    mut v_a_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ =
        l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(
            v_ps_1597_, v_i_1598_, v_a_1599_,
        );
    leanh::lean_dec(v_i_1598_);
    leanh::lean_dec_ref(v_ps_1597_);
    return v_res_1600_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg___boxed(
    mut v_upperBound_1601_: *mut leanh::LeanObject,
    mut v___x_1602_: *mut leanh::LeanObject,
    mut v_ps_1603_: *mut leanh::LeanObject,
    mut v_a_1604_: *mut leanh::LeanObject,
    mut v_b_1605_: *mut leanh::LeanObject,
    mut v___y_1606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_1601_, v___x_1602_, v_ps_1603_, v_a_1604_, v_b_1605_, v___y_1606_);
    leanh::lean_dec_ref(v_ps_1603_);
    leanh::lean_dec_ref(v___x_1602_);
    leanh::lean_dec(v_upperBound_1601_);
    return v_res_1607_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(
    mut v_upperBound_1608_: *mut leanh::LeanObject,
    mut v___x_1609_: *mut leanh::LeanObject,
    mut v_ps_1610_: *mut leanh::LeanObject,
    mut v_inst_1611_: *mut leanh::LeanObject,
    mut v_R_1612_: *mut leanh::LeanObject,
    mut v_a_1613_: *mut leanh::LeanObject,
    mut v_b_1614_: *mut leanh::LeanObject,
    mut v_c_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_1608_, v___x_1609_, v_ps_1610_, v_a_1613_, v_b_1614_, v___y_1616_);
    return v___x_1617_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___boxed(
    mut v_upperBound_1618_: *mut leanh::LeanObject,
    mut v___x_1619_: *mut leanh::LeanObject,
    mut v_ps_1620_: *mut leanh::LeanObject,
    mut v_inst_1621_: *mut leanh::LeanObject,
    mut v_R_1622_: *mut leanh::LeanObject,
    mut v_a_1623_: *mut leanh::LeanObject,
    mut v_b_1624_: *mut leanh::LeanObject,
    mut v_c_1625_: *mut leanh::LeanObject,
    mut v___y_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(v_upperBound_1618_, v___x_1619_, v_ps_1620_, v_inst_1621_, v_R_1622_, v_a_1623_, v_b_1624_, v_c_1625_, v___y_1626_);
    leanh::lean_dec_ref(v_ps_1620_);
    leanh::lean_dec_ref(v___x_1619_);
    leanh::lean_dec(v_upperBound_1618_);
    return v_res_1627_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(
    mut v_upperBound_1628_: *mut leanh::LeanObject,
    mut v_ps_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
    mut v_b_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1633_ = lean_nat_dec_lt(v_a_1630_, v_upperBound_1628_);
                if v___x_1633_ == 0 {
                    leanh::lean_dec(v_a_1630_);
                    v___x_1634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1634_, 0, v_b_1631_);
                    leanh::lean_ctor_set(v___x_1634_, 1, v___y_1632_);
                    return v___x_1634_;
                } else {
                    v___x_1635_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_1629_, v_a_1630_, v___y_1632_);
                    v_snd_1636_ = leanh::lean_ctor_get(v___x_1635_, 1);
                    leanh::lean_inc(v_snd_1636_);
                    leanh::lean_dec_ref(v___x_1635_);
                    v___x_1637_ = leanh::lean_box(0);
                    v___x_1638_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1639_ = lean_nat_add(v_a_1630_, v___x_1638_);
                    leanh::lean_dec(v_a_1630_);
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
    mut v_upperBound_1641_: *mut leanh::LeanObject,
    mut v_ps_1642_: *mut leanh::LeanObject,
    mut v_a_1643_: *mut leanh::LeanObject,
    mut v_b_1644_: *mut leanh::LeanObject,
    mut v___y_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_1641_, v_ps_1642_, v_a_1643_, v_b_1644_, v___y_1645_);
    leanh::lean_dec_ref(v_ps_1642_);
    leanh::lean_dec(v_upperBound_1641_);
    return v_res_1646_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(
    mut v_ps_1647_: *mut leanh::LeanObject,
    mut v_a_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v_unused_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1649_ = lean_array_get_size(v_ps_1647_);
                v___x_1650_ = leanh::lean_unsigned_to_nat(0);
                v___x_1651_ = leanh::lean_box(0);
                v___x_1652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v___x_1649_, v_ps_1647_, v___x_1650_, v___x_1651_, v_a_1648_);
                v_snd_1653_ = leanh::lean_ctor_get(v___x_1652_, 1);
                v_isSharedCheck_1660_ = (!leanh::lean_is_exclusive(v___x_1652_)) as u8;
                if v_isSharedCheck_1660_ == 0 {
                    v_unused_1661_ = leanh::lean_ctor_get(v___x_1652_, 0);
                    leanh::lean_dec(v_unused_1661_);
                    v___x_1655_ = v___x_1652_;
                    v_isShared_1656_ = v_isSharedCheck_1660_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1653_);
                    leanh::lean_dec(v___x_1652_);
                    v___x_1655_ = leanh::lean_box(0);
                    v_isShared_1656_ = v_isSharedCheck_1660_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1656_ == 0 {
                    leanh::lean_ctor_set(v___x_1655_, 0, v___x_1651_);
                    v___x_1658_ = v___x_1655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_snd_1653_);
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
    mut v_ps_1662_: *mut leanh::LeanObject,
    mut v_a_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ =
        l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(
            v_ps_1662_, v_a_1663_,
        );
    leanh::lean_dec_ref(v_ps_1662_);
    return v_res_1664_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(
    mut v_upperBound_1665_: *mut leanh::LeanObject,
    mut v_ps_1666_: *mut leanh::LeanObject,
    mut v_inst_1667_: *mut leanh::LeanObject,
    mut v_R_1668_: *mut leanh::LeanObject,
    mut v_a_1669_: *mut leanh::LeanObject,
    mut v_b_1670_: *mut leanh::LeanObject,
    mut v_c_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_1665_, v_ps_1666_, v_a_1669_, v_b_1670_, v___y_1672_);
    return v___x_1673_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___boxed(
    mut v_upperBound_1674_: *mut leanh::LeanObject,
    mut v_ps_1675_: *mut leanh::LeanObject,
    mut v_inst_1676_: *mut leanh::LeanObject,
    mut v_R_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_b_1679_: *mut leanh::LeanObject,
    mut v_c_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(v_upperBound_1674_, v_ps_1675_, v_inst_1676_, v_R_1677_, v_a_1678_, v_b_1679_, v_c_1680_, v___y_1681_);
    leanh::lean_dec_ref(v_ps_1675_);
    leanh::lean_dec(v_upperBound_1674_);
    return v_res_1682_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(
    mut v_sz_1683_: usize,
    mut v_i_1684_: usize,
    mut v_bs_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1690_: usize = 0;
    let mut v___x_1691_: usize = 0;
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1686_ = lean_usize_dec_lt(v_i_1684_, v_sz_1683_);
                if v___x_1686_ == 0 {
                    return v_bs_1685_;
                } else {
                    v___x_1687_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1688_ = lean_array_uset(v_bs_1685_, v_i_1684_, v___x_1687_);
                    v___x_1689_ = 0;
                    v___x_1690_ = 1usize;
                    v___x_1691_ = lean_usize_add(v_i_1684_, v___x_1690_);
                    v___x_1692_ = leanh::lean_box((v___x_1689_) as usize);
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
    mut v_sz_1695_: *mut leanh::LeanObject,
    mut v_i_1696_: *mut leanh::LeanObject,
    mut v_bs_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1698_: usize = 0;
    let mut v_i_boxed_1699_: usize = 0;
    let mut v_res_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1698_ = leanh::lean_unbox_usize(v_sz_1695_);
    leanh::lean_dec(v_sz_1695_);
    v_i_boxed_1699_ = leanh::lean_unbox_usize(v_i_1696_);
    leanh::lean_dec(v_i_1696_);
    v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_boxed_1698_, v_i_boxed_1699_, v_bs_1697_);
    return v_res_1700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attach(
    mut v_ps_1701_: *mut leanh::LeanObject,
    mut v_k_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1703_: usize = 0;
    let mut v___x_1704_: usize = 0;
    let mut v_visited_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1703_ = lean_array_size(v_ps_1701_);
    v___x_1704_ = 0usize;
    leanh::lean_inc_ref(v_ps_1701_);
    v_visited_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_1703_, v___x_1704_, v_ps_1701_);
    v___x_1706_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1706_, 0, v_k_1702_);
    leanh::lean_ctor_set(v___x_1706_, 1, v_visited_1705_);
    v___x_1707_ =
        l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(
            v_ps_1701_,
            v___x_1706_,
        );
    leanh::lean_dec_ref(v_ps_1701_);
    v_snd_1708_ = leanh::lean_ctor_get(v___x_1707_, 1);
    leanh::lean_inc(v_snd_1708_);
    leanh::lean_dec_ref(v___x_1707_);
    v_fst_1709_ = leanh::lean_ctor_get(v_snd_1708_, 0);
    leanh::lean_inc(v_fst_1709_);
    leanh::lean_dec(v_snd_1708_);
    return v_fst_1709_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
    mut v_fvarId_1710_: *mut leanh::LeanObject,
    mut v_k_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1714_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(
                    v_fvarId_1710_,
                    v_a_1712_,
                );
                if leanh::lean_obj_tag(v___x_1714_) == 0 {
                    v_a_1715_ = leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1723_ = (!leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1723_ == 0 {
                        v___x_1717_ = v___x_1714_;
                        v_isShared_1718_ = v_isSharedCheck_1723_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1715_);
                        leanh::lean_dec(v___x_1714_);
                        v___x_1717_ = leanh::lean_box(0);
                        v_isShared_1718_ = v_isSharedCheck_1723_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_1711_);
                    v_a_1724_ = leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1731_ = (!leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1731_ == 0 {
                        v___x_1726_ = v___x_1714_;
                        v_isShared_1727_ = v_isSharedCheck_1731_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1724_);
                        leanh::lean_dec(v___x_1714_);
                        v___x_1726_ = leanh::lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1731_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1719_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_1715_, v_k_1711_);
                if v_isShared_1718_ == 0 {
                    leanh::lean_ctor_set(v___x_1717_, 0, v___x_1719_);
                    v___x_1721_ = v___x_1717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
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
                    v_reuseFailAlloc_1730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
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
    mut v_fvarId_1732_: *mut leanh::LeanObject,
    mut v_k_1733_: *mut leanh::LeanObject,
    mut v_a_1734_: *mut leanh::LeanObject,
    mut v_a_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
        v_fvarId_1732_,
        v_k_1733_,
        v_a_1734_,
    );
    leanh::lean_dec(v_a_1734_);
    leanh::lean_dec(v_fvarId_1732_);
    return v_res_1736_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(
    mut v_fvarId_1737_: *mut leanh::LeanObject,
    mut v_k_1738_: *mut leanh::LeanObject,
    mut v_a_1739_: *mut leanh::LeanObject,
    mut v_a_1740_: *mut leanh::LeanObject,
    mut v_a_1741_: *mut leanh::LeanObject,
    mut v_a_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
        v_fvarId_1737_,
        v_k_1738_,
        v_a_1739_,
    );
    return v___x_1745_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___boxed(
    mut v_fvarId_1746_: *mut leanh::LeanObject,
    mut v_k_1747_: *mut leanh::LeanObject,
    mut v_a_1748_: *mut leanh::LeanObject,
    mut v_a_1749_: *mut leanh::LeanObject,
    mut v_a_1750_: *mut leanh::LeanObject,
    mut v_a_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(
        v_fvarId_1746_,
        v_k_1747_,
        v_a_1748_,
        v_a_1749_,
        v_a_1750_,
        v_a_1751_,
        v_a_1752_,
    );
    leanh::lean_dec(v_a_1752_);
    leanh::lean_dec_ref(v_a_1751_);
    leanh::lean_dec(v_a_1750_);
    leanh::lean_dec_ref(v_a_1749_);
    leanh::lean_dec(v_a_1748_);
    leanh::lean_dec(v_fvarId_1746_);
    return v_res_1754_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
    mut v_params_1755_: *mut leanh::LeanObject,
    mut v_k_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
    mut v_a_1758_: *mut leanh::LeanObject,
    mut v_a_1759_: *mut leanh::LeanObject,
    mut v_a_1760_: *mut leanh::LeanObject,
    mut v_a_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1772_: u8 = 0;
    let mut v_a_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1763_) == 0 {
                    v_a_1764_ = leanh::lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1772_ = (!leanh::lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1772_ == 0 {
                        v___x_1766_ = v___x_1763_;
                        v_isShared_1767_ = v_isSharedCheck_1772_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1764_);
                        leanh::lean_dec(v___x_1763_);
                        v___x_1766_ = leanh::lean_box(0);
                        v_isShared_1767_ = v_isSharedCheck_1772_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_1756_);
                    v_a_1773_ = leanh::lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1780_ = (!leanh::lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1780_ == 0 {
                        v___x_1775_ = v___x_1763_;
                        v_isShared_1776_ = v_isSharedCheck_1780_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1773_);
                        leanh::lean_dec(v___x_1763_);
                        v___x_1775_ = leanh::lean_box(0);
                        v_isShared_1776_ = v_isSharedCheck_1780_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1768_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_1764_, v_k_1756_);
                if v_isShared_1767_ == 0 {
                    leanh::lean_ctor_set(v___x_1766_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
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
                    v_reuseFailAlloc_1779_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
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
    mut v_params_1781_: *mut leanh::LeanObject,
    mut v_k_1782_: *mut leanh::LeanObject,
    mut v_a_1783_: *mut leanh::LeanObject,
    mut v_a_1784_: *mut leanh::LeanObject,
    mut v_a_1785_: *mut leanh::LeanObject,
    mut v_a_1786_: *mut leanh::LeanObject,
    mut v_a_1787_: *mut leanh::LeanObject,
    mut v_a_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
        v_params_1781_,
        v_k_1782_,
        v_a_1783_,
        v_a_1784_,
        v_a_1785_,
        v_a_1786_,
        v_a_1787_,
    );
    leanh::lean_dec(v_a_1787_);
    leanh::lean_dec_ref(v_a_1786_);
    leanh::lean_dec(v_a_1785_);
    leanh::lean_dec_ref(v_a_1784_);
    leanh::lean_dec(v_a_1783_);
    leanh::lean_dec_ref(v_params_1781_);
    return v_res_1789_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(
    mut v_a_1790_: *mut leanh::LeanObject,
    mut v_a_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isFun_1794_: u8 = 0;
    let mut v_tail_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v_unused_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1790_) == 0 {
                    v___x_1792_ = l_List_reverse___redArg(v_a_1791_);
                    return v___x_1792_;
                } else {
                    v_head_1793_ = leanh::lean_ctor_get(v_a_1790_, 0);
                    v_isFun_1794_ = leanh::lean_ctor_get_uint8(
                        v_head_1793_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    if v_isFun_1794_ == 0 {
                        leanh::lean_inc(v_head_1793_);
                        v_tail_1795_ = leanh::lean_ctor_get(v_a_1790_, 1);
                        v_isSharedCheck_1803_ = (!leanh::lean_is_exclusive(v_a_1790_)) as u8;
                        if v_isSharedCheck_1803_ == 0 {
                            v_unused_1804_ = leanh::lean_ctor_get(v_a_1790_, 0);
                            leanh::lean_dec(v_unused_1804_);
                            v___x_1797_ = v_a_1790_;
                            v_isShared_1798_ = v_isSharedCheck_1803_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_1795_);
                            leanh::lean_dec(v_a_1790_);
                            v___x_1797_ = leanh::lean_box(0);
                            v_isShared_1798_ = v_isSharedCheck_1803_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_tail_1805_ = leanh::lean_ctor_get(v_a_1790_, 1);
                        leanh::lean_inc(v_tail_1805_);
                        leanh::lean_dec_ref_known(v_a_1790_, 2);
                        v_a_1790_ = v_tail_1805_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1798_ == 0 {
                    leanh::lean_ctor_set(v___x_1797_, 1, v_a_1791_);
                    v___x_1800_ = v___x_1797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_head_1793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_a_1791_);
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
    mut v_a_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isFun_1811_: u8 = 0;
    let mut v_tail_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v_unused_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1807_) == 0 {
                    v___x_1809_ = l_List_reverse___redArg(v_a_1808_);
                    return v___x_1809_;
                } else {
                    v_head_1810_ = leanh::lean_ctor_get(v_a_1807_, 0);
                    v_isFun_1811_ = leanh::lean_ctor_get_uint8(
                        v_head_1810_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    if v_isFun_1811_ == 0 {
                        v_tail_1812_ = leanh::lean_ctor_get(v_a_1807_, 1);
                        leanh::lean_inc(v_tail_1812_);
                        leanh::lean_dec_ref_known(v_a_1807_, 2);
                        v_a_1807_ = v_tail_1812_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_head_1810_);
                        v_tail_1814_ = leanh::lean_ctor_get(v_a_1807_, 1);
                        v_isSharedCheck_1822_ = (!leanh::lean_is_exclusive(v_a_1807_)) as u8;
                        if v_isSharedCheck_1822_ == 0 {
                            v_unused_1823_ = leanh::lean_ctor_get(v_a_1807_, 0);
                            leanh::lean_dec(v_unused_1823_);
                            v___x_1816_ = v_a_1807_;
                            v_isShared_1817_ = v_isSharedCheck_1822_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_1814_);
                            leanh::lean_dec(v_a_1807_);
                            v___x_1816_ = leanh::lean_box(0);
                            v_isShared_1817_ = v_isSharedCheck_1822_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1817_ == 0 {
                    leanh::lean_ctor_set(v___x_1816_, 1, v_a_1808_);
                    v___x_1819_ = v___x_1816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_head_1810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_a_1808_);
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
    mut v_k_1824_: *mut leanh::LeanObject,
    mut v_a_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_a_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1827_ = lean_st_ref_get(v_a_1825_);
                v___x_1828_ = lean_st_ref_take(v_a_1825_);
                v___x_1829_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v___x_1834_) == 0 {
                    v_a_1835_ = leanh::lean_ctor_get(v___x_1834_, 0);
                    v_isSharedCheck_1843_ = (!leanh::lean_is_exclusive(v___x_1834_)) as u8;
                    if v_isSharedCheck_1843_ == 0 {
                        v___x_1837_ = v___x_1834_;
                        v_isShared_1838_ = v_isSharedCheck_1843_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1835_);
                        leanh::lean_dec(v___x_1834_);
                        v___x_1837_ = leanh::lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1843_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_1824_);
                    v_a_1844_ = leanh::lean_ctor_get(v___x_1834_, 0);
                    v_isSharedCheck_1851_ = (!leanh::lean_is_exclusive(v___x_1834_)) as u8;
                    if v_isSharedCheck_1851_ == 0 {
                        v___x_1846_ = v___x_1834_;
                        v_isShared_1847_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1844_);
                        leanh::lean_dec(v___x_1834_);
                        v___x_1846_ = leanh::lean_box(0);
                        v_isShared_1847_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1839_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_1835_, v_k_1824_);
                if v_isShared_1838_ == 0 {
                    leanh::lean_ctor_set(v___x_1837_, 0, v___x_1839_);
                    v___x_1841_ = v___x_1837_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
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
                    v_reuseFailAlloc_1850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
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
    mut v_k_1852_: *mut leanh::LeanObject,
    mut v_a_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_1852_, v_a_1853_);
    leanh::lean_dec(v_a_1853_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachJps(
    mut v_k_1856_: *mut leanh::LeanObject,
    mut v_a_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
    mut v_a_1860_: *mut leanh::LeanObject,
    mut v_a_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_1856_, v_a_1857_);
    return v___x_1863_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_attachJps___boxed(
    mut v_k_1864_: *mut leanh::LeanObject,
    mut v_a_1865_: *mut leanh::LeanObject,
    mut v_a_1866_: *mut leanh::LeanObject,
    mut v_a_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
    mut v_a_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps(
        v_k_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_,
    );
    leanh::lean_dec(v_a_1869_);
    leanh::lean_dec_ref(v_a_1868_);
    leanh::lean_dec(v_a_1867_);
    leanh::lean_dec_ref(v_a_1866_);
    leanh::lean_dec(v_a_1865_);
    return v_res_1871_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_addToPull(
    mut v_isFun_1872_: u8,
    mut v_decl_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
    mut v_a_1877_: *mut leanh::LeanObject,
    mut v_a_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v_value_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut v_a_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_a_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut v_a_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = lean_st_ref_get(v_a_1874_);
                v___x_1881_ = lean_st_ref_take(v_a_1874_);
                leanh::lean_dec(v___x_1881_);
                v___x_1882_ = leanh::lean_box(0);
                v___x_1883_ = lean_st_ref_set(v_a_1874_, v___x_1882_);
                v_params_1884_ = leanh::lean_ctor_get(v_decl_1873_, 2);
                leanh::lean_inc_ref(v_params_1884_);
                v_type_1885_ = leanh::lean_ctor_get(v_decl_1873_, 3);
                leanh::lean_inc_ref(v_type_1885_);
                v_value_1886_ = leanh::lean_ctor_get(v_decl_1873_, 4);
                leanh::lean_inc_ref(v_value_1886_);
                v___x_1887_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                    v_value_1886_,
                    v_a_1874_,
                    v_a_1875_,
                    v_a_1876_,
                    v_a_1877_,
                    v_a_1878_,
                );
                if leanh::lean_obj_tag(v___x_1887_) == 0 {
                    v_a_1888_ = leanh::lean_ctor_get(v___x_1887_, 0);
                    leanh::lean_inc(v_a_1888_);
                    leanh::lean_dec_ref_known(v___x_1887_, 1);
                    v___x_1889_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
                        v_params_1884_,
                        v_a_1888_,
                        v_a_1874_,
                        v_a_1875_,
                        v_a_1876_,
                        v_a_1877_,
                        v_a_1878_,
                    );
                    if leanh::lean_obj_tag(v___x_1889_) == 0 {
                        v_a_1890_ = leanh::lean_ctor_get(v___x_1889_, 0);
                        leanh::lean_inc(v_a_1890_);
                        leanh::lean_dec_ref_known(v___x_1889_, 1);
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
                            if leanh::lean_obj_tag(v___x_1921_) == 0 {
                                v_a_1922_ = leanh::lean_ctor_get(v___x_1921_, 0);
                                leanh::lean_inc(v_a_1922_);
                                leanh::lean_dec_ref_known(v___x_1921_, 1);
                                v_value_1894_ = v_a_1922_;
                                v___y_1895_ = v_a_1874_;
                                v___y_1896_ = v_a_1876_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_type_1885_);
                                leanh::lean_dec_ref(v_params_1884_);
                                leanh::lean_dec(v___x_1880_);
                                leanh::lean_dec_ref(v_decl_1873_);
                                v_a_1923_ = leanh::lean_ctor_get(v___x_1921_, 0);
                                v_isSharedCheck_1930_ =
                                    (!leanh::lean_is_exclusive(v___x_1921_)) as u8;
                                if v_isSharedCheck_1930_ == 0 {
                                    v___x_1925_ = v___x_1921_;
                                    v_isShared_1926_ = v_isSharedCheck_1930_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1923_);
                                    leanh::lean_dec(v___x_1921_);
                                    v___x_1925_ = leanh::lean_box(0);
                                    v_isShared_1926_ = v_isSharedCheck_1930_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_type_1885_);
                        leanh::lean_dec_ref(v_params_1884_);
                        leanh::lean_dec(v___x_1880_);
                        leanh::lean_dec_ref(v_decl_1873_);
                        v_a_1931_ = leanh::lean_ctor_get(v___x_1889_, 0);
                        v_isSharedCheck_1938_ =
                            (!leanh::lean_is_exclusive(v___x_1889_)) as u8;
                        if v_isSharedCheck_1938_ == 0 {
                            v___x_1933_ = v___x_1889_;
                            v_isShared_1934_ = v_isSharedCheck_1938_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1931_);
                            leanh::lean_dec(v___x_1889_);
                            v___x_1933_ = leanh::lean_box(0);
                            v_isShared_1934_ = v_isSharedCheck_1938_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_type_1885_);
                    leanh::lean_dec_ref(v_params_1884_);
                    leanh::lean_dec(v___x_1880_);
                    leanh::lean_dec_ref(v_decl_1873_);
                    v_a_1939_ = leanh::lean_ctor_get(v___x_1887_, 0);
                    v_isSharedCheck_1946_ = (!leanh::lean_is_exclusive(v___x_1887_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1941_ = v___x_1887_;
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1939_);
                        leanh::lean_dec(v___x_1887_);
                        v___x_1941_ = leanh::lean_box(0);
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1897_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1892_, v_decl_1873_, v_type_1885_, v_params_1884_, v_value_1894_, v___y_1896_);
                if leanh::lean_obj_tag(v___x_1897_) == 0 {
                    v_a_1898_ = leanh::lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1912_ = (!leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1912_ == 0 {
                        v___x_1900_ = v___x_1897_;
                        v_isShared_1901_ = v_isSharedCheck_1912_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1898_);
                        leanh::lean_dec(v___x_1897_);
                        v___x_1900_ = leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1912_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1880_);
                    v_a_1913_ = leanh::lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1920_ = (!leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1920_ == 0 {
                        v___x_1915_ = v___x_1897_;
                        v_isShared_1916_ = v_isSharedCheck_1920_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1913_);
                        leanh::lean_dec(v___x_1897_);
                        v___x_1915_ = leanh::lean_box(0);
                        v_isShared_1916_ = v_isSharedCheck_1920_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1902_ = lean_st_ref_take(v___y_1895_);
                leanh::lean_inc(v_a_1898_);
                v___x_1903_ =
                    l_Lean_Compiler_LCNF_FunDecl_collectUsed(v___x_1892_, v_a_1898_, v___x_1891_);
                v___x_1904_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1904_, 0, v_a_1898_);
                leanh::lean_ctor_set(v___x_1904_, 1, v___x_1903_);
                leanh::lean_ctor_set_uint8(
                    v___x_1904_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_isFun_1872_,
                );
                v___x_1905_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                leanh::lean_ctor_set(v___x_1905_, 1, v___x_1902_);
                v___x_1906_ = l_List_appendTR___redArg(v___x_1905_, v___x_1880_);
                v___x_1907_ = lean_st_ref_set(v___y_1895_, v___x_1906_);
                v___x_1908_ = leanh::lean_box(0);
                if v_isShared_1901_ == 0 {
                    leanh::lean_ctor_set(v___x_1900_, 0, v___x_1908_);
                    v___x_1910_ = v___x_1900_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
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
                    v_reuseFailAlloc_1919_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
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
                    v_reuseFailAlloc_1929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
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
                    v_reuseFailAlloc_1937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
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
                    v_reuseFailAlloc_1945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
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
    mut v_code_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
    mut v_a_1951_: *mut leanh::LeanObject,
    mut v_a_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___y_1965_: u8 = 0;
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut v_unused_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: usize = 0;
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: u8 = 0;
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_decl_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_decl_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2012_: u8 = 0;
    let mut v_cases_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: usize = 0;
    let mut v___x_2028_: usize = 0;
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut v_unused_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v_a_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_code_1947_) {
                0 => {
                    v_decl_1954_ = leanh::lean_ctor_get(v_code_1947_, 0);
                    v_k_1955_ = leanh::lean_ctor_get(v_code_1947_, 1);
                    leanh::lean_inc_ref(v_k_1955_);
                    v___x_1956_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                        v_k_1955_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_,
                    );
                    if leanh::lean_obj_tag(v___x_1956_) == 0 {
                        v_a_1957_ = leanh::lean_ctor_get(v___x_1956_, 0);
                        leanh::lean_inc(v_a_1957_);
                        leanh::lean_dec_ref_known(v___x_1956_, 1);
                        v_fvarId_1958_ = leanh::lean_ctor_get(v_decl_1954_, 0);
                        v___x_1959_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(
                            v_fvarId_1958_,
                            v_a_1957_,
                            v_a_1948_,
                        );
                        if leanh::lean_obj_tag(v___x_1959_) == 0 {
                            v_a_1960_ = leanh::lean_ctor_get(v___x_1959_, 0);
                            v_isSharedCheck_1986_ =
                                (!leanh::lean_is_exclusive(v___x_1959_)) as u8;
                            if v_isSharedCheck_1986_ == 0 {
                                v___x_1962_ = v___x_1959_;
                                v_isShared_1963_ = v_isSharedCheck_1986_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1960_);
                                leanh::lean_dec(v___x_1959_);
                                v___x_1962_ = leanh::lean_box(0);
                                v_isShared_1963_ = v_isSharedCheck_1986_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_code_1947_, 2);
                            return v___x_1959_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_code_1947_, 2);
                        return v___x_1956_;
                    }
                }
                1 => {
                    v_decl_1987_ = leanh::lean_ctor_get(v_code_1947_, 0);
                    leanh::lean_inc_ref(v_decl_1987_);
                    v_k_1988_ = leanh::lean_ctor_get(v_code_1947_, 1);
                    leanh::lean_inc_ref(v_k_1988_);
                    leanh::lean_dec_ref_known(v_code_1947_, 2);
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
                    if leanh::lean_obj_tag(v___x_1990_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1990_, 1);
                        v_code_1947_ = v_k_1988_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_1988_);
                        v_a_1992_ = leanh::lean_ctor_get(v___x_1990_, 0);
                        v_isSharedCheck_1999_ =
                            (!leanh::lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_1999_ == 0 {
                            v___x_1994_ = v___x_1990_;
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1992_);
                            leanh::lean_dec(v___x_1990_);
                            v___x_1994_ = leanh::lean_box(0);
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 7;
                            continue;
                        }
                    }
                }
                2 => {
                    v_decl_2000_ = leanh::lean_ctor_get(v_code_1947_, 0);
                    leanh::lean_inc_ref(v_decl_2000_);
                    v_k_2001_ = leanh::lean_ctor_get(v_code_1947_, 1);
                    leanh::lean_inc_ref(v_k_2001_);
                    leanh::lean_dec_ref_known(v_code_1947_, 2);
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
                    if leanh::lean_obj_tag(v___x_2003_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2003_, 1);
                        v_code_1947_ = v_k_2001_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_2001_);
                        v_a_2005_ = leanh::lean_ctor_get(v___x_2003_, 0);
                        v_isSharedCheck_2012_ =
                            (!leanh::lean_is_exclusive(v___x_2003_)) as u8;
                        if v_isSharedCheck_2012_ == 0 {
                            v___x_2007_ = v___x_2003_;
                            v_isShared_2008_ = v_isSharedCheck_2012_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2005_);
                            leanh::lean_dec(v___x_2003_);
                            v___x_2007_ = leanh::lean_box(0);
                            v_isShared_2008_ = v_isSharedCheck_2012_;
                            state = 9;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_2013_ = leanh::lean_ctor_get(v_code_1947_, 0);
                    leanh::lean_inc_ref(v_cases_2013_);
                    v_typeName_2014_ = leanh::lean_ctor_get(v_cases_2013_, 0);
                    v_resultType_2015_ = leanh::lean_ctor_get(v_cases_2013_, 1);
                    v_discr_2016_ = leanh::lean_ctor_get(v_cases_2013_, 2);
                    v_alts_2017_ = leanh::lean_ctor_get(v_cases_2013_, 3);
                    v_isSharedCheck_2056_ = (!leanh::lean_is_exclusive(v_cases_2013_)) as u8;
                    if v_isSharedCheck_2056_ == 0 {
                        v___x_2019_ = v_cases_2013_;
                        v_isShared_2020_ = v_isSharedCheck_2056_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_alts_2017_);
                        leanh::lean_inc(v_discr_2016_);
                        leanh::lean_inc(v_resultType_2015_);
                        leanh::lean_inc(v_typeName_2014_);
                        leanh::lean_dec(v_cases_2013_);
                        v___x_2019_ = leanh::lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2056_;
                        state = 11;
                        continue;
                    }
                }
                _ => {
                    v___x_2057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2057_, 0, v_code_1947_);
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
                    leanh::lean_inc_ref(v_decl_1954_);
                    v_isSharedCheck_1975_ = (!leanh::lean_is_exclusive(v_code_1947_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v_unused_1976_ = leanh::lean_ctor_get(v_code_1947_, 1);
                        leanh::lean_dec(v_unused_1976_);
                        v_unused_1977_ = leanh::lean_ctor_get(v_code_1947_, 0);
                        leanh::lean_dec(v_unused_1977_);
                        v___x_1967_ = v_code_1947_;
                        v_isShared_1968_ = v_isSharedCheck_1975_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1947_);
                        v___x_1967_ = leanh::lean_box(0);
                        v_isShared_1968_ = v_isSharedCheck_1975_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1960_);
                    if v_isShared_1963_ == 0 {
                        leanh::lean_ctor_set(v___x_1962_, 0, v_code_1947_);
                        v___x_1979_ = v___x_1962_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1980_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_code_1947_);
                        v___x_1979_ = v_reuseFailAlloc_1980_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1968_ == 0 {
                    leanh::lean_ctor_set(v___x_1967_, 1, v_a_1960_);
                    v___x_1970_ = v___x_1967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_decl_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_a_1960_);
                    v___x_1970_ = v_reuseFailAlloc_1974_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1963_ == 0 {
                    leanh::lean_ctor_set(v___x_1962_, 0, v___x_1970_);
                    v___x_1972_ = v___x_1962_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
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
                    v_reuseFailAlloc_1998_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
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
                    v_reuseFailAlloc_2011_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
                    v___x_2010_ = v_reuseFailAlloc_2011_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2010_;
            }
            11 => {
                v___x_2021_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_alts_2017_);
                v___x_2022_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v___x_2021_, v_alts_2017_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
                if leanh::lean_obj_tag(v___x_2022_) == 0 {
                    v_a_2023_ = leanh::lean_ctor_get(v___x_2022_, 0);
                    v_isSharedCheck_2047_ = (!leanh::lean_is_exclusive(v___x_2022_)) as u8;
                    if v_isSharedCheck_2047_ == 0 {
                        v___x_2025_ = v___x_2022_;
                        v_isShared_2026_ = v_isSharedCheck_2047_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2023_);
                        leanh::lean_dec(v___x_2022_);
                        v___x_2025_ = leanh::lean_box(0);
                        v_isShared_2026_ = v_isSharedCheck_2047_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2019_);
                    leanh::lean_dec_ref(v_alts_2017_);
                    leanh::lean_dec(v_discr_2016_);
                    leanh::lean_dec_ref(v_resultType_2015_);
                    leanh::lean_dec(v_typeName_2014_);
                    leanh::lean_dec_ref_known(v_code_1947_, 1);
                    v_a_2048_ = leanh::lean_ctor_get(v___x_2022_, 0);
                    v_isSharedCheck_2055_ = (!leanh::lean_is_exclusive(v___x_2022_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v___x_2050_ = v___x_2022_;
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2048_);
                        leanh::lean_dec(v___x_2022_);
                        v___x_2050_ = leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 18;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2027_ = lean_ptr_addr(v_alts_2017_);
                leanh::lean_dec_ref(v_alts_2017_);
                v___x_2028_ = lean_ptr_addr(v_a_2023_);
                v___x_2029_ = lean_usize_dec_eq(v___x_2027_, v___x_2028_);
                if v___x_2029_ == 0 {
                    v_isSharedCheck_2042_ = (!leanh::lean_is_exclusive(v_code_1947_)) as u8;
                    if v_isSharedCheck_2042_ == 0 {
                        v_unused_2043_ = leanh::lean_ctor_get(v_code_1947_, 0);
                        leanh::lean_dec(v_unused_2043_);
                        v___x_2031_ = v_code_1947_;
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1947_);
                        v___x_2031_ = leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2023_);
                    leanh::lean_del_object(v___x_2019_);
                    leanh::lean_dec(v_discr_2016_);
                    leanh::lean_dec_ref(v_resultType_2015_);
                    leanh::lean_dec(v_typeName_2014_);
                    if v_isShared_2026_ == 0 {
                        leanh::lean_ctor_set(v___x_2025_, 0, v_code_1947_);
                        v___x_2045_ = v___x_2025_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2046_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_code_1947_);
                        v___x_2045_ = v_reuseFailAlloc_2046_;
                        state = 17;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_2020_ == 0 {
                    leanh::lean_ctor_set(v___x_2019_, 3, v_a_2023_);
                    v___x_2034_ = v___x_2019_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_typeName_2014_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_resultType_2015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_discr_2016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_a_2023_);
                    v___x_2034_ = v_reuseFailAlloc_2041_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2032_ == 0 {
                    leanh::lean_ctor_set(v___x_2031_, 0, v___x_2034_);
                    v___x_2036_ = v___x_2031_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2034_);
                    v___x_2036_ = v_reuseFailAlloc_2040_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2026_ == 0 {
                    leanh::lean_ctor_set(v___x_2025_, 0, v___x_2036_);
                    v___x_2038_ = v___x_2025_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2039_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
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
                    v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
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
    mut v_i_2058_: *mut leanh::LeanObject,
    mut v_as_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: usize = 0;
    let mut v___x_2073_: usize = 0;
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2092_: u8 = 0;
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v_a_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut v_code_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2066_ = lean_array_get_size(v_as_2059_);
                v___x_2067_ = lean_nat_dec_lt(v_i_2058_, v___x_2066_);
                if v___x_2067_ == 0 {
                    leanh::lean_dec(v_i_2058_);
                    v___x_2068_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2068_, 0, v_as_2059_);
                    return v___x_2068_;
                } else {
                    v_a_2069_ = lean_array_fget_borrowed(v_as_2059_, v_i_2058_);
                    if leanh::lean_obj_tag(v_a_2069_) == 0 {
                        v_params_2082_ = leanh::lean_ctor_get(v_a_2069_, 1);
                        v_code_2083_ = leanh::lean_ctor_get(v_a_2069_, 2);
                        leanh::lean_inc_ref(v_code_2083_);
                        v___x_2084_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                            v_code_2083_,
                            v___y_2060_,
                            v___y_2061_,
                            v___y_2062_,
                            v___y_2063_,
                            v___y_2064_,
                        );
                        if leanh::lean_obj_tag(v___x_2084_) == 0 {
                            v_a_2085_ = leanh::lean_ctor_get(v___x_2084_, 0);
                            leanh::lean_inc(v_a_2085_);
                            leanh::lean_dec_ref_known(v___x_2084_, 1);
                            v___x_2086_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(
                                v_params_2082_,
                                v_a_2085_,
                                v___y_2060_,
                                v___y_2061_,
                                v___y_2062_,
                                v___y_2063_,
                                v___y_2064_,
                            );
                            if leanh::lean_obj_tag(v___x_2086_) == 0 {
                                v_a_2087_ = leanh::lean_ctor_get(v___x_2086_, 0);
                                leanh::lean_inc(v_a_2087_);
                                leanh::lean_dec_ref_known(v___x_2086_, 1);
                                leanh::lean_inc_ref(v_a_2069_);
                                v___x_2088_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2069_, v_a_2087_);
                                v_a_2071_ = v___x_2088_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_as_2059_);
                                leanh::lean_dec(v_i_2058_);
                                v_a_2089_ = leanh::lean_ctor_get(v___x_2086_, 0);
                                v_isSharedCheck_2096_ =
                                    (!leanh::lean_is_exclusive(v___x_2086_)) as u8;
                                if v_isSharedCheck_2096_ == 0 {
                                    v___x_2091_ = v___x_2086_;
                                    v_isShared_2092_ = v_isSharedCheck_2096_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2089_);
                                    leanh::lean_dec(v___x_2086_);
                                    v___x_2091_ = leanh::lean_box(0);
                                    v_isShared_2092_ = v_isSharedCheck_2096_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_as_2059_);
                            leanh::lean_dec(v_i_2058_);
                            v_a_2097_ = leanh::lean_ctor_get(v___x_2084_, 0);
                            v_isSharedCheck_2104_ =
                                (!leanh::lean_is_exclusive(v___x_2084_)) as u8;
                            if v_isSharedCheck_2104_ == 0 {
                                v___x_2099_ = v___x_2084_;
                                v_isShared_2100_ = v_isSharedCheck_2104_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2097_);
                                leanh::lean_dec(v___x_2084_);
                                v___x_2099_ = leanh::lean_box(0);
                                v_isShared_2100_ = v_isSharedCheck_2104_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_code_2105_ = leanh::lean_ctor_get(v_a_2069_, 0);
                        leanh::lean_inc_ref(v_code_2105_);
                        v___x_2106_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
                            v_code_2105_,
                            v___y_2060_,
                            v___y_2061_,
                            v___y_2062_,
                            v___y_2063_,
                            v___y_2064_,
                        );
                        if leanh::lean_obj_tag(v___x_2106_) == 0 {
                            v_a_2107_ = leanh::lean_ctor_get(v___x_2106_, 0);
                            leanh::lean_inc(v_a_2107_);
                            leanh::lean_dec_ref_known(v___x_2106_, 1);
                            leanh::lean_inc_ref(v_a_2069_);
                            v___x_2108_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2069_, v_a_2107_);
                            v_a_2071_ = v___x_2108_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_as_2059_);
                            leanh::lean_dec(v_i_2058_);
                            v_a_2109_ = leanh::lean_ctor_get(v___x_2106_, 0);
                            v_isSharedCheck_2116_ =
                                (!leanh::lean_is_exclusive(v___x_2106_)) as u8;
                            if v_isSharedCheck_2116_ == 0 {
                                v___x_2111_ = v___x_2106_;
                                v_isShared_2112_ = v_isSharedCheck_2116_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2109_);
                                leanh::lean_dec(v___x_2106_);
                                v___x_2111_ = leanh::lean_box(0);
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
                    v___x_2075_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2076_ = lean_nat_add(v_i_2058_, v___x_2075_);
                    v___x_2077_ = lean_array_fset(v_as_2059_, v_i_2058_, v_a_2071_);
                    leanh::lean_dec(v_i_2058_);
                    v_i_2058_ = v___x_2076_;
                    v_as_2059_ = v___x_2077_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_a_2071_);
                    v___x_2079_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2080_ = lean_nat_add(v_i_2058_, v___x_2079_);
                    leanh::lean_dec(v_i_2058_);
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
                    v_reuseFailAlloc_2095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
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
                    v_reuseFailAlloc_2103_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
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
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
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
    mut v_i_2117_: *mut leanh::LeanObject,
    mut v_as_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
    mut v___y_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2125_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v_i_2117_, v_as_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
    leanh::lean_dec(v___y_2123_);
    leanh::lean_dec_ref(v___y_2122_);
    leanh::lean_dec(v___y_2121_);
    leanh::lean_dec_ref(v___y_2120_);
    leanh::lean_dec(v___y_2119_);
    return v_res_2125_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_addToPull___boxed(
    mut v_isFun_2126_: *mut leanh::LeanObject,
    mut v_decl_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
    mut v_a_2129_: *mut leanh::LeanObject,
    mut v_a_2130_: *mut leanh::LeanObject,
    mut v_a_2131_: *mut leanh::LeanObject,
    mut v_a_2132_: *mut leanh::LeanObject,
    mut v_a_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isFun_boxed_2134_: u8 = 0;
    let mut v_res_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isFun_boxed_2134_ = (leanh::lean_unbox(v_isFun_2126_) as u8);
    v_res_2135_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(
        v_isFun_boxed_2134_,
        v_decl_2127_,
        v_a_2128_,
        v_a_2129_,
        v_a_2130_,
        v_a_2131_,
        v_a_2132_,
    );
    leanh::lean_dec(v_a_2132_);
    leanh::lean_dec_ref(v_a_2131_);
    leanh::lean_dec(v_a_2130_);
    leanh::lean_dec_ref(v_a_2129_);
    leanh::lean_dec(v_a_2128_);
    return v_res_2135_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed(
    mut v_code_2136_: *mut leanh::LeanObject,
    mut v_a_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
    mut v_a_2139_: *mut leanh::LeanObject,
    mut v_a_2140_: *mut leanh::LeanObject,
    mut v_a_2141_: *mut leanh::LeanObject,
    mut v_a_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(
        v_code_2136_,
        v_a_2137_,
        v_a_2138_,
        v_a_2139_,
        v_a_2140_,
        v_a_2141_,
    );
    leanh::lean_dec(v_a_2141_);
    leanh::lean_dec_ref(v_a_2140_);
    leanh::lean_dec(v_a_2139_);
    leanh::lean_dec_ref(v_a_2138_);
    leanh::lean_dec(v_a_2137_);
    return v_res_2143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(
    mut v_f_2144_: *mut leanh::LeanObject,
    mut v_v_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2160_: u8 = 0;
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_2145_) == 0 {
                    v_code_2152_ = leanh::lean_ctor_get(v_v_2145_, 0);
                    v_isSharedCheck_2176_ = (!leanh::lean_is_exclusive(v_v_2145_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v___x_2154_ = v_v_2145_;
                        v_isShared_2155_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_code_2152_);
                        leanh::lean_dec(v_v_2145_);
                        v___x_2154_ = leanh::lean_box(0);
                        v_isShared_2155_ = v_isSharedCheck_2176_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_2144_);
                    v___x_2177_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2177_, 0, v_v_2145_);
                    return v___x_2177_;
                }
            }
            1 => {
                leanh::lean_inc(v___y_2150_);
                leanh::lean_inc_ref(v___y_2149_);
                leanh::lean_inc(v___y_2148_);
                leanh::lean_inc_ref(v___y_2147_);
                leanh::lean_inc(v___y_2146_);
                v___x_2156_ = leanh::lean_apply_7(
                    v_f_2144_,
                    v_code_2152_,
                    v___y_2146_,
                    v___y_2147_,
                    v___y_2148_,
                    v___y_2149_,
                    v___y_2150_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2156_) == 0 {
                    v_a_2157_ = leanh::lean_ctor_get(v___x_2156_, 0);
                    v_isSharedCheck_2167_ = (!leanh::lean_is_exclusive(v___x_2156_)) as u8;
                    if v_isSharedCheck_2167_ == 0 {
                        v___x_2159_ = v___x_2156_;
                        v_isShared_2160_ = v_isSharedCheck_2167_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2157_);
                        leanh::lean_dec(v___x_2156_);
                        v___x_2159_ = leanh::lean_box(0);
                        v_isShared_2160_ = v_isSharedCheck_2167_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2154_);
                    v_a_2168_ = leanh::lean_ctor_get(v___x_2156_, 0);
                    v_isSharedCheck_2175_ = (!leanh::lean_is_exclusive(v___x_2156_)) as u8;
                    if v_isSharedCheck_2175_ == 0 {
                        v___x_2170_ = v___x_2156_;
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2168_);
                        leanh::lean_dec(v___x_2156_);
                        v___x_2170_ = leanh::lean_box(0);
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2155_ == 0 {
                    leanh::lean_ctor_set(v___x_2154_, 0, v_a_2157_);
                    v___x_2162_ = v___x_2154_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2166_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2157_);
                    v___x_2162_ = v_reuseFailAlloc_2166_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2160_ == 0 {
                    leanh::lean_ctor_set(v___x_2159_, 0, v___x_2162_);
                    v___x_2164_ = v___x_2159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
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
                    v_reuseFailAlloc_2174_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
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
    mut v_f_2178_: *mut leanh::LeanObject,
    mut v_v_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
    mut v___y_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2186_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_2178_, v_v_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
    leanh::lean_dec(v___y_2184_);
    leanh::lean_dec_ref(v___y_2183_);
    leanh::lean_dec(v___y_2182_);
    leanh::lean_dec_ref(v___y_2181_);
    leanh::lean_dec(v___y_2180_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(
    mut v_pu_2187_: u8,
    mut v_f_2188_: *mut leanh::LeanObject,
    mut v_v_2189_: *mut leanh::LeanObject,
    mut v___y_2190_: *mut leanh::LeanObject,
    mut v___y_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
    mut v___y_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_2188_, v_v_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
    return v___x_2196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___boxed(
    mut v_pu_2197_: *mut leanh::LeanObject,
    mut v_f_2198_: *mut leanh::LeanObject,
    mut v_v_2199_: *mut leanh::LeanObject,
    mut v___y_2200_: *mut leanh::LeanObject,
    mut v___y_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
    mut v___y_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
    mut v___y_2205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_2206_: u8 = 0;
    let mut v_res_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2206_ = (leanh::lean_unbox(v_pu_2197_) as u8);
    v_res_2207_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(v_pu_boxed_2206_, v_f_2198_, v_v_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
    leanh::lean_dec(v___y_2204_);
    leanh::lean_dec_ref(v___y_2203_);
    leanh::lean_dec(v___y_2202_);
    leanh::lean_dec_ref(v___y_2201_);
    leanh::lean_dec(v___y_2200_);
    return v_res_2207_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullFunDecls(
    mut v_decl_2209_: *mut leanh::LeanObject,
    mut v_a_2210_: *mut leanh::LeanObject,
    mut v_a_2211_: *mut leanh::LeanObject,
    mut v_a_2212_: *mut leanh::LeanObject,
    mut v_a_2213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_2219_: u8 = 0;
    let mut v_inlineAttr_x3f_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_a_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2215_ = leanh::lean_box(0);
                v___x_2216_ = lean_st_mk_ref(v___x_2215_);
                v_toSignature_2217_ = leanh::lean_ctor_get(v_decl_2209_, 0);
                v_value_2218_ = leanh::lean_ctor_get(v_decl_2209_, 1);
                v_recursive_2219_ = leanh::lean_ctor_get_uint8(
                    v_decl_2209_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_2220_ = leanh::lean_ctor_get(v_decl_2209_, 2);
                v_isSharedCheck_2249_ = (!leanh::lean_is_exclusive(v_decl_2209_)) as u8;
                if v_isSharedCheck_2249_ == 0 {
                    v___x_2222_ = v_decl_2209_;
                    v_isShared_2223_ = v_isSharedCheck_2249_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inlineAttr_x3f_2220_);
                    leanh::lean_inc(v_value_2218_);
                    leanh::lean_inc(v_toSignature_2217_);
                    leanh::lean_dec(v_decl_2209_);
                    v___x_2222_ = leanh::lean_box(0);
                    v_isShared_2223_ = v_isSharedCheck_2249_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2224_ = l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0;
                v___x_2225_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v___x_2224_, v_value_2218_, v___x_2216_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
                if leanh::lean_obj_tag(v___x_2225_) == 0 {
                    v_a_2226_ = leanh::lean_ctor_get(v___x_2225_, 0);
                    v_isSharedCheck_2240_ = (!leanh::lean_is_exclusive(v___x_2225_)) as u8;
                    if v_isSharedCheck_2240_ == 0 {
                        v___x_2228_ = v___x_2225_;
                        v_isShared_2229_ = v_isSharedCheck_2240_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2226_);
                        leanh::lean_dec(v___x_2225_);
                        v___x_2228_ = leanh::lean_box(0);
                        v_isShared_2229_ = v_isSharedCheck_2240_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2222_);
                    leanh::lean_dec(v_inlineAttr_x3f_2220_);
                    leanh::lean_dec_ref(v_toSignature_2217_);
                    leanh::lean_dec(v___x_2216_);
                    v_a_2241_ = leanh::lean_ctor_get(v___x_2225_, 0);
                    v_isSharedCheck_2248_ = (!leanh::lean_is_exclusive(v___x_2225_)) as u8;
                    if v_isSharedCheck_2248_ == 0 {
                        v___x_2243_ = v___x_2225_;
                        v_isShared_2244_ = v_isSharedCheck_2248_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2241_);
                        leanh::lean_dec(v___x_2225_);
                        v___x_2243_ = leanh::lean_box(0);
                        v_isShared_2244_ = v_isSharedCheck_2248_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2230_ = lean_st_ref_get(v___x_2216_);
                leanh::lean_dec(v___x_2216_);
                v___x_2231_ = lean_array_mk(v___x_2230_);
                v___x_2232_ = leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_PullFunDecls_attach as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___x_2232_, 0, v___x_2231_);
                v___x_2233_ =
                    l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(v___x_2232_, v_a_2226_);
                if v_isShared_2223_ == 0 {
                    leanh::lean_ctor_set(v___x_2222_, 1, v___x_2233_);
                    v___x_2235_ = v___x_2222_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_toSignature_2217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_inlineAttr_x3f_2220_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2239_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_recursive_2219_,
                    );
                    v___x_2235_ = v_reuseFailAlloc_2239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2229_ == 0 {
                    leanh::lean_ctor_set(v___x_2228_, 0, v___x_2235_);
                    v___x_2237_ = v___x_2228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
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
                    v_reuseFailAlloc_2247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
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
    mut v_decl_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
    mut v_a_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
    mut v_a_2254_: *mut leanh::LeanObject,
    mut v_a_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_Compiler_LCNF_Decl_pullFunDecls(
        v_decl_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
    );
    leanh::lean_dec(v_a_2254_);
    leanh::lean_dec_ref(v_a_2253_);
    leanh::lean_dec(v_a_2252_);
    leanh::lean_dec_ref(v_a_2251_);
    return v_res_2256_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = leanh::lean_unsigned_to_nat(0);
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_pullFunDecls() -> *mut leanh::LeanObject {
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_pullFunDecls___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_pullFunDecls___closed__3_once),
        _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3,
    );
    return v___x_2266_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_;
    v___x_2338_ = 1;
    v___x_2339_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_;
    v___x_2340_ = l_Lean_registerTraceClass(v___x_2337_, v___x_2338_, v___x_2339_);
    return v___x_2340_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2____boxed(
    mut v_a_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2342_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
    return v_res_2342_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default =
        _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default();
    leanh::lean_mark_persistent(
        l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default,
    );
    l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull =
        _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull);
    l_Lean_Compiler_LCNF_pullFunDecls = _init_l_Lean_Compiler_LCNF_pullFunDecls();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls);
    res = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PullFunDecls(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_PullFunDecls(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
}