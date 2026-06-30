// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MatchDiscrOnly
// Imports: Lean.Meta.Tactic.Simp.Simproc Init.Grind.Util Init.Simproc Lean.Meta.Tactic.Simp.Rewrite
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_set,
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_find_expr, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_ptr_addr, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash,
    l_Lean_instBEqBinderInfo_beq, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppM, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkExpectedPropHint,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::l_Lean_Meta_Match_Extension_getMatcherInfo_x3f;
use crate::r#gen::Lean::Meta::Tactic::Simp::Rewrite::{
    initialize_Lean_Meta_Tactic_Simp_Rewrite, l_Lean_Meta_Simp_simpMatchDiscrs_x3f,
    runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_Simprocs_add,
    l_Lean_Meta_Simp_registerBuiltinSimproc, runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
pub static l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        115, 105, 109, 112, 77, 97, 116, 99, 104, 68, 105, 115, 99, 114, 115, 79, 110, 108, 121, 0,
    ],
};
static mut l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2_value)
            as *mut leanh::LeanObject,
        170869938317263309 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [114, 101, 100, 117, 99, 101, 83, 105, 109, 112, 77, 97, 116, 99, 104, 68, 105, 115, 99, 114, 115, 79, 110, 108, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject,9841915364091332459 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value: leanh::LeanArrayObject<3> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_isSimpMatchDiscrsOnly___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2_value:
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
    m_fun: l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(
    mut v_e_1159_: *mut leanh::LeanObject,
    mut v_a_1160_: *mut leanh::LeanObject,
    mut v_a_1161_: *mut leanh::LeanObject,
    mut v_a_1162_: *mut leanh::LeanObject,
    mut v_a_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3;
    v___x_1166_ = leanh::lean_unsigned_to_nat(1);
    v___x_1167_ = lean_mk_empty_array_with_capacity(v___x_1166_);
    v___x_1168_ = lean_array_push(v___x_1167_, v_e_1159_);
    v___x_1169_ = l_Lean_Meta_mkAppM(
        v___x_1165_,
        v___x_1168_,
        v_a_1160_,
        v_a_1161_,
        v_a_1162_,
        v_a_1163_,
    );
    return v___x_1169_;
}
pub unsafe fn l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___boxed(
    mut v_e_1170_: *mut leanh::LeanObject,
    mut v_a_1171_: *mut leanh::LeanObject,
    mut v_a_1172_: *mut leanh::LeanObject,
    mut v_a_1173_: *mut leanh::LeanObject,
    mut v_a_1174_: *mut leanh::LeanObject,
    mut v_a_1175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(
        v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_,
    );
    leanh::lean_dec(v_a_1174_);
    leanh::lean_dec_ref(v_a_1173_);
    leanh::lean_dec(v_a_1172_);
    leanh::lean_dec_ref(v_a_1171_);
    return v_res_1176_;
}
pub unsafe fn l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(
    mut v_e_1177_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u8 = 0;
    v___x_1178_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3;
    v___x_1179_ = leanh::lean_unsigned_to_nat(2);
    v___x_1180_ = l_Lean_Expr_isAppOfArity(v_e_1177_, v___x_1178_, v___x_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Lean_Meta_Grind_isSimpMatchDiscrsOnly___boxed(
    mut v_e_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: u8 = 0;
    let mut v_r_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(v_e_1181_);
    leanh::lean_dec_ref(v_e_1181_);
    v_r_1183_ = leanh::lean_box((v_res_1182_) as usize);
    return v_r_1183_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(
    mut v_declName_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = lean_st_ref_get(v___y_1185_);
    v_env_1188_ = leanh::lean_ctor_get(v___x_1187_, 0);
    leanh::lean_inc_ref(v_env_1188_);
    leanh::lean_dec(v___x_1187_);
    v___x_1189_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1188_, v_declName_1184_);
    v___x_1190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1190_, 0, v___x_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg___boxed(
    mut v_declName_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_1191_, v___y_1192_);
    leanh::lean_dec(v___y_1192_);
    return v_res_1194_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(
    mut v_declName_1195_: *mut leanh::LeanObject,
    mut v___y_1196_: *mut leanh::LeanObject,
    mut v___y_1197_: *mut leanh::LeanObject,
    mut v___y_1198_: *mut leanh::LeanObject,
    mut v___y_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
    mut v___y_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_1195_, v___y_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___boxed(
    mut v_declName_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
    mut v___y_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
    mut v___y_1211_: *mut leanh::LeanObject,
    mut v___y_1212_: *mut leanh::LeanObject,
    mut v___y_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1214_ =
        l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(
            v_declName_1205_,
            v___y_1206_,
            v___y_1207_,
            v___y_1208_,
            v___y_1209_,
            v___y_1210_,
            v___y_1211_,
            v___y_1212_,
        );
    leanh::lean_dec(v___y_1212_);
    leanh::lean_dec_ref(v___y_1211_);
    leanh::lean_dec(v___y_1210_);
    leanh::lean_dec_ref(v___y_1209_);
    leanh::lean_dec(v___y_1208_);
    leanh::lean_dec_ref(v___y_1207_);
    leanh::lean_dec(v___y_1206_);
    return v_res_1214_;
}
pub unsafe fn l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(
    mut v_e_1217_: *mut leanh::LeanObject,
    mut v_a_1218_: *mut leanh::LeanObject,
    mut v_a_1219_: *mut leanh::LeanObject,
    mut v_a_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
    mut v_a_1222_: *mut leanh::LeanObject,
    mut v_a_1223_: *mut leanh::LeanObject,
    mut v_a_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: u8 = 0;
    let mut v_arg_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: u8 = 0;
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: u8 = 0;
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v_val_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1254_: u8 = 0;
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v_val_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1263_: u8 = 0;
    let mut v_expr_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1266_: u8 = 0;
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_a_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_isSharedCheck_1293_: u8 = 0;
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_a_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1324_: u8 = 0;
    let mut v_a_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1217_);
                v___x_1226_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1217_, v_a_1222_);
                if leanh::lean_obj_tag(v___x_1226_) == 0 {
                    v_a_1227_ = leanh::lean_ctor_get(v___x_1226_, 0);
                    v_isSharedCheck_1324_ = (!leanh::lean_is_exclusive(v___x_1226_)) as u8;
                    if v_isSharedCheck_1324_ == 0 {
                        v___x_1229_ = v___x_1226_;
                        v_isShared_1230_ = v_isSharedCheck_1324_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1227_);
                        leanh::lean_dec(v___x_1226_);
                        v___x_1229_ = leanh::lean_box(0);
                        v_isShared_1230_ = v_isSharedCheck_1324_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1217_);
                    v_a_1325_ = leanh::lean_ctor_get(v___x_1226_, 0);
                    v_isSharedCheck_1332_ = (!leanh::lean_is_exclusive(v___x_1226_)) as u8;
                    if v_isSharedCheck_1332_ == 0 {
                        v___x_1327_ = v___x_1226_;
                        v_isShared_1328_ = v_isSharedCheck_1332_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1325_);
                        leanh::lean_dec(v___x_1226_);
                        v___x_1327_ = leanh::lean_box(0);
                        v_isShared_1328_ = v_isSharedCheck_1332_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1236_ = l_Lean_Expr_cleanupAnnotations(v_a_1227_);
                v___x_1237_ = l_Lean_Expr_isApp(v___x_1236_);
                if v___x_1237_ == 0 {
                    leanh::lean_dec_ref(v___x_1236_);
                    leanh::lean_dec_ref(v_e_1217_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1238_ = leanh::lean_ctor_get(v___x_1236_, 1);
                    leanh::lean_inc_ref(v_arg_1238_);
                    v___x_1239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1236_);
                    v___x_1240_ = l_Lean_Expr_isApp(v___x_1239_);
                    if v___x_1240_ == 0 {
                        leanh::lean_dec_ref(v___x_1239_);
                        leanh::lean_dec_ref(v_arg_1238_);
                        leanh::lean_dec_ref(v_e_1217_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1239_);
                        v___x_1242_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3;
                        v___x_1243_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1242_);
                        leanh::lean_dec_ref(v___x_1241_);
                        if v___x_1243_ == 0 {
                            leanh::lean_dec_ref(v_arg_1238_);
                            leanh::lean_dec_ref(v_e_1217_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_1229_);
                            v___x_1244_ = l_Lean_Expr_getAppFn(v_arg_1238_);
                            if leanh::lean_obj_tag(v___x_1244_) == 4 {
                                v_declName_1245_ = leanh::lean_ctor_get(v___x_1244_, 0);
                                leanh::lean_inc(v_declName_1245_);
                                leanh::lean_dec_ref_known(v___x_1244_, 2);
                                v___x_1246_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_1245_, v_a_1224_);
                                v_a_1247_ = leanh::lean_ctor_get(v___x_1246_, 0);
                                v_isSharedCheck_1319_ =
                                    (!leanh::lean_is_exclusive(v___x_1246_)) as u8;
                                if v_isSharedCheck_1319_ == 0 {
                                    v___x_1249_ = v___x_1246_;
                                    v_isShared_1250_ = v_isSharedCheck_1319_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1247_);
                                    leanh::lean_dec(v___x_1246_);
                                    v___x_1249_ = leanh::lean_box(0);
                                    v_isShared_1250_ = v_isSharedCheck_1319_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1244_);
                                leanh::lean_dec_ref(v_arg_1238_);
                                v___x_1320_ = leanh::lean_box(0);
                                v___x_1321_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                leanh::lean_ctor_set(v___x_1321_, 0, v_e_1217_);
                                leanh::lean_ctor_set(v___x_1321_, 1, v___x_1320_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_1321_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                    v___x_1243_,
                                );
                                v___x_1322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1322_, 0, v___x_1321_);
                                v___x_1323_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1323_, 0, v___x_1322_);
                                return v___x_1323_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1232_ = l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0;
                if v_isShared_1230_ == 0 {
                    leanh::lean_ctor_set(v___x_1229_, 0, v___x_1232_);
                    v___x_1234_ = v___x_1229_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1235_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
                    v___x_1234_ = v_reuseFailAlloc_1235_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1234_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_1247_) == 1 {
                    leanh::lean_del_object(v___x_1249_);
                    v_val_1251_ = leanh::lean_ctor_get(v_a_1247_, 0);
                    v_isSharedCheck_1312_ = (!leanh::lean_is_exclusive(v_a_1247_)) as u8;
                    if v_isSharedCheck_1312_ == 0 {
                        v___x_1253_ = v_a_1247_;
                        v_isShared_1254_ = v_isSharedCheck_1312_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1251_);
                        leanh::lean_dec(v_a_1247_);
                        v___x_1253_ = leanh::lean_box(0);
                        v_isShared_1254_ = v_isSharedCheck_1312_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1247_);
                    leanh::lean_dec_ref(v_arg_1238_);
                    v___x_1313_ = leanh::lean_box(0);
                    v___x_1314_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_1314_, 0, v_e_1217_);
                    leanh::lean_ctor_set(v___x_1314_, 1, v___x_1313_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1314_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_1243_,
                    );
                    v___x_1315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1315_, 0, v___x_1314_);
                    if v_isShared_1250_ == 0 {
                        leanh::lean_ctor_set(v___x_1249_, 0, v___x_1315_);
                        v___x_1317_ = v___x_1249_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_1318_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
                        v___x_1317_ = v_reuseFailAlloc_1318_;
                        state = 19;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1255_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(
                    v_val_1251_,
                    v_arg_1238_,
                    v_a_1218_,
                    v_a_1219_,
                    v_a_1220_,
                    v_a_1221_,
                    v_a_1222_,
                    v_a_1223_,
                    v_a_1224_,
                );
                if leanh::lean_obj_tag(v___x_1255_) == 0 {
                    v_a_1256_ = leanh::lean_ctor_get(v___x_1255_, 0);
                    v_isSharedCheck_1303_ = (!leanh::lean_is_exclusive(v___x_1255_)) as u8;
                    if v_isSharedCheck_1303_ == 0 {
                        v___x_1258_ = v___x_1255_;
                        v_isShared_1259_ = v_isSharedCheck_1303_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1256_);
                        leanh::lean_dec(v___x_1255_);
                        v___x_1258_ = leanh::lean_box(0);
                        v_isShared_1259_ = v_isSharedCheck_1303_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1253_);
                    leanh::lean_dec_ref(v_e_1217_);
                    v_a_1304_ = leanh::lean_ctor_get(v___x_1255_, 0);
                    v_isSharedCheck_1311_ = (!leanh::lean_is_exclusive(v___x_1255_)) as u8;
                    if v_isSharedCheck_1311_ == 0 {
                        v___x_1306_ = v___x_1255_;
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1304_);
                        leanh::lean_dec(v___x_1255_);
                        v___x_1306_ = leanh::lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 17;
                        continue;
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_a_1256_) == 1 {
                    leanh::lean_del_object(v___x_1258_);
                    leanh::lean_del_object(v___x_1253_);
                    leanh::lean_dec_ref(v_e_1217_);
                    v_val_1260_ = leanh::lean_ctor_get(v_a_1256_, 0);
                    v_isSharedCheck_1294_ = (!leanh::lean_is_exclusive(v_a_1256_)) as u8;
                    if v_isSharedCheck_1294_ == 0 {
                        v___x_1262_ = v_a_1256_;
                        v_isShared_1263_ = v_isSharedCheck_1294_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1260_);
                        leanh::lean_dec(v_a_1256_);
                        v___x_1262_ = leanh::lean_box(0);
                        v_isShared_1263_ = v_isSharedCheck_1294_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1256_);
                    v___x_1295_ = leanh::lean_box(0);
                    v___x_1296_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_1296_, 0, v_e_1217_);
                    leanh::lean_ctor_set(v___x_1296_, 1, v___x_1295_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1296_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_1243_,
                    );
                    if v_isShared_1254_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1253_, 0);
                        leanh::lean_ctor_set(v___x_1253_, 0, v___x_1296_);
                        v___x_1298_ = v___x_1253_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1296_);
                        v___x_1298_ = v_reuseFailAlloc_1302_;
                        state = 15;
                        continue;
                    }
                }
            }
            7 => {
                v_expr_1264_ = leanh::lean_ctor_get(v_val_1260_, 0);
                v_proof_x3f_1265_ = leanh::lean_ctor_get(v_val_1260_, 1);
                v_cache_1266_ = leanh::lean_ctor_get_uint8(
                    v_val_1260_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_1293_ = (!leanh::lean_is_exclusive(v_val_1260_)) as u8;
                if v_isSharedCheck_1293_ == 0 {
                    v___x_1268_ = v_val_1260_;
                    v_isShared_1269_ = v_isSharedCheck_1293_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_proof_x3f_1265_);
                    leanh::lean_inc(v_expr_1264_);
                    leanh::lean_dec(v_val_1260_);
                    v___x_1268_ = leanh::lean_box(0);
                    v_isShared_1269_ = v_isSharedCheck_1293_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1270_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(
                    v_expr_1264_,
                    v_a_1221_,
                    v_a_1222_,
                    v_a_1223_,
                    v_a_1224_,
                );
                if leanh::lean_obj_tag(v___x_1270_) == 0 {
                    v_a_1271_ = leanh::lean_ctor_get(v___x_1270_, 0);
                    v_isSharedCheck_1284_ = (!leanh::lean_is_exclusive(v___x_1270_)) as u8;
                    if v_isSharedCheck_1284_ == 0 {
                        v___x_1273_ = v___x_1270_;
                        v_isShared_1274_ = v_isSharedCheck_1284_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1271_);
                        leanh::lean_dec(v___x_1270_);
                        v___x_1273_ = leanh::lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1284_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1268_);
                    leanh::lean_dec(v_proof_x3f_1265_);
                    leanh::lean_del_object(v___x_1262_);
                    v_a_1285_ = leanh::lean_ctor_get(v___x_1270_, 0);
                    v_isSharedCheck_1292_ = (!leanh::lean_is_exclusive(v___x_1270_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1287_ = v___x_1270_;
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1285_);
                        leanh::lean_dec(v___x_1270_);
                        v___x_1287_ = leanh::lean_box(0);
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 13;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1269_ == 0 {
                    leanh::lean_ctor_set(v___x_1268_, 0, v_a_1271_);
                    v___x_1276_ = v___x_1268_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_proof_x3f_1265_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1283_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_cache_1266_,
                    );
                    v___x_1276_ = v_reuseFailAlloc_1283_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1263_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1262_, 0);
                    leanh::lean_ctor_set(v___x_1262_, 0, v___x_1276_);
                    v___x_1278_ = v___x_1262_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
                    v___x_1278_ = v_reuseFailAlloc_1282_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1274_ == 0 {
                    leanh::lean_ctor_set(v___x_1273_, 0, v___x_1278_);
                    v___x_1280_ = v___x_1273_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1281_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
                    v___x_1280_ = v_reuseFailAlloc_1281_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1280_;
            }
            13 => {
                if v_isShared_1288_ == 0 {
                    v___x_1290_ = v___x_1287_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
                    v___x_1290_ = v_reuseFailAlloc_1291_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1290_;
            }
            15 => {
                if v_isShared_1259_ == 0 {
                    leanh::lean_ctor_set(v___x_1258_, 0, v___x_1298_);
                    v___x_1300_ = v___x_1258_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
                    v___x_1300_ = v_reuseFailAlloc_1301_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1300_;
            }
            17 => {
                if v_isShared_1307_ == 0 {
                    v___x_1309_ = v___x_1306_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
                    v___x_1309_ = v_reuseFailAlloc_1310_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1309_;
            }
            19 => {
                return v___x_1317_;
            }
            20 => {
                if v_isShared_1328_ == 0 {
                    v___x_1330_ = v___x_1327_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
                    v___x_1330_ = v_reuseFailAlloc_1331_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed(
    mut v_e_1333_: *mut leanh::LeanObject,
    mut v_a_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
    mut v_a_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(
        v_e_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_,
    );
    leanh::lean_dec(v_a_1340_);
    leanh::lean_dec_ref(v_a_1339_);
    leanh::lean_dec(v_a_1338_);
    leanh::lean_dec_ref(v_a_1337_);
    leanh::lean_dec(v_a_1336_);
    leanh::lean_dec_ref(v_a_1335_);
    leanh::lean_dec(v_a_1334_);
    return v_res_1342_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_()
-> *mut leanh::LeanObject {
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1361_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_;
    v___x_1362_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_;
    v___x_1363_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1364_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1361_, v___x_1362_, v___x_1363_);
    return v___x_1364_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10____boxed(
    mut v_a_1365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1366_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_();
    return v_res_1366_;
}
pub unsafe fn l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(
    mut v_s_1367_: *mut leanh::LeanObject,
    mut v_a_1368_: *mut leanh::LeanObject,
    mut v_a_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_;
    v___x_1372_ = 0;
    v___x_1373_ =
        l_Lean_Meta_Simp_Simprocs_add(v_s_1367_, v___x_1371_, v___x_1372_, v_a_1368_, v_a_1369_);
    return v___x_1373_;
}
pub unsafe fn l_Lean_Meta_Grind_addSimpMatchDiscrsOnly___boxed(
    mut v_s_1374_: *mut leanh::LeanObject,
    mut v_a_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
    mut v_a_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1378_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(v_s_1374_, v_a_1375_, v_a_1376_);
    leanh::lean_dec(v_a_1376_);
    leanh::lean_dec_ref(v_a_1375_);
    return v_res_1378_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(
    mut v_e_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut v_arg_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: u8 = 0;
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1379_);
                v___x_1389_ = l_Lean_Expr_cleanupAnnotations(v_e_1379_);
                v___x_1390_ = l_Lean_Expr_isApp(v___x_1389_);
                if v___x_1390_ == 0 {
                    leanh::lean_dec_ref(v___x_1389_);
                    state = 1;
                    continue;
                } else {
                    v_arg_1391_ = leanh::lean_ctor_get(v___x_1389_, 1);
                    leanh::lean_inc_ref(v_arg_1391_);
                    v___x_1392_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1389_);
                    v___x_1393_ = l_Lean_Expr_isApp(v___x_1392_);
                    if v___x_1393_ == 0 {
                        leanh::lean_dec_ref(v___x_1392_);
                        leanh::lean_dec_ref(v_arg_1391_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1392_);
                        v___x_1395_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3;
                        v___x_1396_ = l_Lean_Expr_isConstOf(v___x_1394_, v___x_1395_);
                        leanh::lean_dec_ref(v___x_1394_);
                        if v___x_1396_ == 0 {
                            leanh::lean_dec_ref(v_arg_1391_);
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_e_1379_);
                            v___x_1397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1397_, 0, v_arg_1391_);
                            v___x_1398_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1398_, 0, v___x_1397_);
                            v___x_1399_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1399_, 0, v___x_1398_);
                            return v___x_1399_;
                        }
                    }
                }
            }
            1 => {
                v___x_1386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1386_, 0, v_e_1379_);
                v___x_1387_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1387_, 0, v___x_1386_);
                v___x_1388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1388_, 0, v___x_1387_);
                return v___x_1388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0___boxed(
    mut v_e_1400_: *mut leanh::LeanObject,
    mut v___y_1401_: *mut leanh::LeanObject,
    mut v___y_1402_: *mut leanh::LeanObject,
    mut v___y_1403_: *mut leanh::LeanObject,
    mut v___y_1404_: *mut leanh::LeanObject,
    mut v___y_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(
        v_e_1400_,
        v___y_1401_,
        v___y_1402_,
        v___y_1403_,
        v___y_1404_,
    );
    leanh::lean_dec(v___y_1404_);
    leanh::lean_dec_ref(v___y_1403_);
    leanh::lean_dec(v___y_1402_);
    leanh::lean_dec_ref(v___y_1401_);
    return v_res_1406_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(
    mut v_e_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
    mut v___y_1410_: *mut leanh::LeanObject,
    mut v___y_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1413_, 0, v_e_1407_);
    v___x_1414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1414_, 0, v___x_1413_);
    return v___x_1414_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1___boxed(
    mut v_e_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
    mut v___y_1419_: *mut leanh::LeanObject,
    mut v___y_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(
        v_e_1415_,
        v___y_1416_,
        v___y_1417_,
        v___y_1418_,
        v___y_1419_,
    );
    leanh::lean_dec(v___y_1419_);
    leanh::lean_dec_ref(v___y_1418_);
    leanh::lean_dec(v___y_1417_);
    leanh::lean_dec_ref(v___y_1416_);
    return v_res_1421_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(
    mut v_00_u03b1_1422_: *mut leanh::LeanObject,
    mut v_x_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
    mut v___y_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = leanh::lean_apply_1(v_x_1423_, leanh::lean_box(0));
    v___x_1430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0___boxed(
    mut v_00_u03b1_1431_: *mut leanh::LeanObject,
    mut v_x_1432_: *mut leanh::LeanObject,
    mut v___y_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
    mut v___y_1436_: *mut leanh::LeanObject,
    mut v___y_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1438_ =
        l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(
            v_00_u03b1_1431_,
            v_x_1432_,
            v___y_1433_,
            v___y_1434_,
            v___y_1435_,
            v___y_1436_,
        );
    leanh::lean_dec(v___y_1436_);
    leanh::lean_dec_ref(v___y_1435_);
    leanh::lean_dec(v___y_1434_);
    leanh::lean_dec_ref(v___y_1433_);
    return v_res_1438_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_x_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1440_) == 0 {
                    v___x_1441_ = leanh::lean_box(0);
                    return v___x_1441_;
                } else {
                    v_key_1442_ = leanh::lean_ctor_get(v_x_1440_, 0);
                    v_value_1443_ = leanh::lean_ctor_get(v_x_1440_, 1);
                    v_tail_1444_ = leanh::lean_ctor_get(v_x_1440_, 2);
                    v___x_1445_ = l_Lean_ExprStructEq_beq(v_key_1442_, v_a_1439_);
                    if v___x_1445_ == 0 {
                        v_x_1440_ = v_tail_1444_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1443_);
                        v___x_1447_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1447_, 0, v_value_1443_);
                        return v___x_1447_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_a_1448_: *mut leanh::LeanObject,
    mut v_x_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1448_, v_x_1449_);
    leanh::lean_dec(v_x_1449_);
    leanh::lean_dec_ref(v_a_1448_);
    return v_res_1450_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(
    mut v_m_1451_: *mut leanh::LeanObject,
    mut v_a_1452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u64 = 0;
    let mut v___x_1456_: u64 = 0;
    let mut v___x_1457_: u64 = 0;
    let mut v_fold_1458_: u64 = 0;
    let mut v___x_1459_: u64 = 0;
    let mut v___x_1460_: u64 = 0;
    let mut v___x_1461_: u64 = 0;
    let mut v___x_1462_: usize = 0;
    let mut v___x_1463_: usize = 0;
    let mut v___x_1464_: usize = 0;
    let mut v___x_1465_: usize = 0;
    let mut v___x_1466_: usize = 0;
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1453_ = leanh::lean_ctor_get(v_m_1451_, 1);
    v___x_1454_ = lean_array_get_size(v_buckets_1453_);
    v___x_1455_ = l_Lean_ExprStructEq_hash(v_a_1452_);
    v___x_1456_ = 32u64;
    v___x_1457_ = lean_uint64_shift_right(v___x_1455_, v___x_1456_);
    v_fold_1458_ = lean_uint64_xor(v___x_1455_, v___x_1457_);
    v___x_1459_ = 16u64;
    v___x_1460_ = lean_uint64_shift_right(v_fold_1458_, v___x_1459_);
    v___x_1461_ = lean_uint64_xor(v_fold_1458_, v___x_1460_);
    v___x_1462_ = lean_uint64_to_usize(v___x_1461_);
    v___x_1463_ = lean_usize_of_nat(v___x_1454_);
    v___x_1464_ = 1usize;
    v___x_1465_ = lean_usize_sub(v___x_1463_, v___x_1464_);
    v___x_1466_ = lean_usize_land(v___x_1462_, v___x_1465_);
    v___x_1467_ = lean_array_uget_borrowed(v_buckets_1453_, v___x_1466_);
    v___x_1468_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1452_, v___x_1467_);
    return v___x_1468_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_m_1469_: *mut leanh::LeanObject,
    mut v_a_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_1469_, v_a_1470_);
    leanh::lean_dec_ref(v_a_1470_);
    leanh::lean_dec_ref(v_m_1469_);
    return v_res_1471_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_a_1472_: *mut leanh::LeanObject,
    mut v_b_1473_: *mut leanh::LeanObject,
    mut v_x_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1474_) == 0 {
                    leanh::lean_dec(v_b_1473_);
                    leanh::lean_dec_ref(v_a_1472_);
                    return v_x_1474_;
                } else {
                    v_key_1475_ = leanh::lean_ctor_get(v_x_1474_, 0);
                    v_value_1476_ = leanh::lean_ctor_get(v_x_1474_, 1);
                    v_tail_1477_ = leanh::lean_ctor_get(v_x_1474_, 2);
                    v_isSharedCheck_1489_ = (!leanh::lean_is_exclusive(v_x_1474_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1479_ = v_x_1474_;
                        v_isShared_1480_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1477_);
                        leanh::lean_inc(v_value_1476_);
                        leanh::lean_inc(v_key_1475_);
                        leanh::lean_dec(v_x_1474_);
                        v___x_1479_ = leanh::lean_box(0);
                        v_isShared_1480_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1481_ = l_Lean_ExprStructEq_beq(v_key_1475_, v_a_1472_);
                if v___x_1481_ == 0 {
                    v___x_1482_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1472_, v_b_1473_, v_tail_1477_);
                    if v_isShared_1480_ == 0 {
                        leanh::lean_ctor_set(v___x_1479_, 2, v___x_1482_);
                        v___x_1484_ = v___x_1479_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1485_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_key_1475_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_value_1476_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 2, v___x_1482_);
                        v___x_1484_ = v_reuseFailAlloc_1485_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1476_);
                    leanh::lean_dec(v_key_1475_);
                    if v_isShared_1480_ == 0 {
                        leanh::lean_ctor_set(v___x_1479_, 1, v_b_1473_);
                        leanh::lean_ctor_set(v___x_1479_, 0, v_a_1472_);
                        v___x_1487_ = v___x_1479_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1488_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1472_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_b_1473_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_tail_1477_);
                        v___x_1487_ = v_reuseFailAlloc_1488_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1484_;
            }
            3 => {
                return v___x_1487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(
    mut v_x_1490_: *mut leanh::LeanObject,
    mut v_x_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u64 = 0;
    let mut v___x_1500_: u64 = 0;
    let mut v___x_1501_: u64 = 0;
    let mut v_fold_1502_: u64 = 0;
    let mut v___x_1503_: u64 = 0;
    let mut v___x_1504_: u64 = 0;
    let mut v___x_1505_: u64 = 0;
    let mut v___x_1506_: usize = 0;
    let mut v___x_1507_: usize = 0;
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: usize = 0;
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1491_) == 0 {
                    return v_x_1490_;
                } else {
                    v_key_1492_ = leanh::lean_ctor_get(v_x_1491_, 0);
                    v_value_1493_ = leanh::lean_ctor_get(v_x_1491_, 1);
                    v_tail_1494_ = leanh::lean_ctor_get(v_x_1491_, 2);
                    v_isSharedCheck_1517_ = (!leanh::lean_is_exclusive(v_x_1491_)) as u8;
                    if v_isSharedCheck_1517_ == 0 {
                        v___x_1496_ = v_x_1491_;
                        v_isShared_1497_ = v_isSharedCheck_1517_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1494_);
                        leanh::lean_inc(v_value_1493_);
                        leanh::lean_inc(v_key_1492_);
                        leanh::lean_dec(v_x_1491_);
                        v___x_1496_ = leanh::lean_box(0);
                        v_isShared_1497_ = v_isSharedCheck_1517_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1498_ = lean_array_get_size(v_x_1490_);
                v___x_1499_ = l_Lean_ExprStructEq_hash(v_key_1492_);
                v___x_1500_ = 32u64;
                v___x_1501_ = lean_uint64_shift_right(v___x_1499_, v___x_1500_);
                v_fold_1502_ = lean_uint64_xor(v___x_1499_, v___x_1501_);
                v___x_1503_ = 16u64;
                v___x_1504_ = lean_uint64_shift_right(v_fold_1502_, v___x_1503_);
                v___x_1505_ = lean_uint64_xor(v_fold_1502_, v___x_1504_);
                v___x_1506_ = lean_uint64_to_usize(v___x_1505_);
                v___x_1507_ = lean_usize_of_nat(v___x_1498_);
                v___x_1508_ = 1usize;
                v___x_1509_ = lean_usize_sub(v___x_1507_, v___x_1508_);
                v___x_1510_ = lean_usize_land(v___x_1506_, v___x_1509_);
                v___x_1511_ = lean_array_uget_borrowed(v_x_1490_, v___x_1510_);
                leanh::lean_inc(v___x_1511_);
                if v_isShared_1497_ == 0 {
                    leanh::lean_ctor_set(v___x_1496_, 2, v___x_1511_);
                    v___x_1513_ = v___x_1496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1516_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_key_1492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_value_1493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1516_, 2, v___x_1511_);
                    v___x_1513_ = v_reuseFailAlloc_1516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1514_ = lean_array_uset(v_x_1490_, v___x_1510_, v___x_1513_);
                v_x_1490_ = v___x_1514_;
                v_x_1491_ = v_tail_1494_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(
    mut v_i_1518_: *mut leanh::LeanObject,
    mut v_source_1519_: *mut leanh::LeanObject,
    mut v_target_1520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v_es_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1521_ = lean_array_get_size(v_source_1519_);
                v___x_1522_ = lean_nat_dec_lt(v_i_1518_, v___x_1521_);
                if v___x_1522_ == 0 {
                    leanh::lean_dec_ref(v_source_1519_);
                    leanh::lean_dec(v_i_1518_);
                    return v_target_1520_;
                } else {
                    v_es_1523_ = lean_array_fget(v_source_1519_, v_i_1518_);
                    v___x_1524_ = leanh::lean_box(0);
                    v_source_1525_ = lean_array_fset(v_source_1519_, v_i_1518_, v___x_1524_);
                    v_target_1526_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1520_, v_es_1523_);
                    v___x_1527_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1528_ = lean_nat_add(v_i_1518_, v___x_1527_);
                    leanh::lean_dec(v_i_1518_);
                    v_i_1518_ = v___x_1528_;
                    v_source_1519_ = v_source_1525_;
                    v_target_1520_ = v_target_1526_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(
    mut v_data_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = lean_array_get_size(v_data_1530_);
    v___x_1532_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1533_ = lean_nat_mul(v___x_1531_, v___x_1532_);
    v___x_1534_ = leanh::lean_unsigned_to_nat(0);
    v___x_1535_ = leanh::lean_box(0);
    v___x_1536_ = lean_mk_array(v_nbuckets_1533_, v___x_1535_);
    v___x_1537_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1534_, v_data_1530_, v___x_1536_);
    return v___x_1537_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(
    mut v_a_1538_: *mut leanh::LeanObject,
    mut v_x_1539_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1540_: u8 = 0;
    let mut v_key_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1539_) == 0 {
                    v___x_1540_ = 0;
                    return v___x_1540_;
                } else {
                    v_key_1541_ = leanh::lean_ctor_get(v_x_1539_, 0);
                    v_tail_1542_ = leanh::lean_ctor_get(v_x_1539_, 2);
                    v___x_1543_ = l_Lean_ExprStructEq_beq(v_key_1541_, v_a_1538_);
                    if v___x_1543_ == 0 {
                        v_x_1539_ = v_tail_1542_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1543_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg___boxed(
    mut v_a_1545_: *mut leanh::LeanObject,
    mut v_x_1546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1547_: u8 = 0;
    let mut v_r_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1545_, v_x_1546_);
    leanh::lean_dec(v_x_1546_);
    leanh::lean_dec_ref(v_a_1545_);
    v_r_1548_ = leanh::lean_box((v_res_1547_) as usize);
    return v_r_1548_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(
    mut v_m_1549_: *mut leanh::LeanObject,
    mut v_a_1550_: *mut leanh::LeanObject,
    mut v_b_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u64 = 0;
    let mut v___x_1559_: u64 = 0;
    let mut v___x_1560_: u64 = 0;
    let mut v_fold_1561_: u64 = 0;
    let mut v___x_1562_: u64 = 0;
    let mut v___x_1563_: u64 = 0;
    let mut v___x_1564_: u64 = 0;
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: usize = 0;
    let mut v___x_1568_: usize = 0;
    let mut v___x_1569_: usize = 0;
    let mut v_bkt_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v_val_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1552_ = leanh::lean_ctor_get(v_m_1549_, 0);
                v_buckets_1553_ = leanh::lean_ctor_get(v_m_1549_, 1);
                v_isSharedCheck_1596_ = (!leanh::lean_is_exclusive(v_m_1549_)) as u8;
                if v_isSharedCheck_1596_ == 0 {
                    v___x_1555_ = v_m_1549_;
                    v_isShared_1556_ = v_isSharedCheck_1596_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1553_);
                    leanh::lean_inc(v_size_1552_);
                    leanh::lean_dec(v_m_1549_);
                    v___x_1555_ = leanh::lean_box(0);
                    v_isShared_1556_ = v_isSharedCheck_1596_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1557_ = lean_array_get_size(v_buckets_1553_);
                v___x_1558_ = l_Lean_ExprStructEq_hash(v_a_1550_);
                v___x_1559_ = 32u64;
                v___x_1560_ = lean_uint64_shift_right(v___x_1558_, v___x_1559_);
                v_fold_1561_ = lean_uint64_xor(v___x_1558_, v___x_1560_);
                v___x_1562_ = 16u64;
                v___x_1563_ = lean_uint64_shift_right(v_fold_1561_, v___x_1562_);
                v___x_1564_ = lean_uint64_xor(v_fold_1561_, v___x_1563_);
                v___x_1565_ = lean_uint64_to_usize(v___x_1564_);
                v___x_1566_ = lean_usize_of_nat(v___x_1557_);
                v___x_1567_ = 1usize;
                v___x_1568_ = lean_usize_sub(v___x_1566_, v___x_1567_);
                v___x_1569_ = lean_usize_land(v___x_1565_, v___x_1568_);
                v_bkt_1570_ = lean_array_uget_borrowed(v_buckets_1553_, v___x_1569_);
                v___x_1571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1550_, v_bkt_1570_);
                if v___x_1571_ == 0 {
                    v___x_1572_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1573_ = lean_nat_add(v_size_1552_, v___x_1572_);
                    leanh::lean_dec(v_size_1552_);
                    leanh::lean_inc(v_bkt_1570_);
                    v___x_1574_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1574_, 0, v_a_1550_);
                    leanh::lean_ctor_set(v___x_1574_, 1, v_b_1551_);
                    leanh::lean_ctor_set(v___x_1574_, 2, v_bkt_1570_);
                    v_buckets_x27_1575_ =
                        lean_array_uset(v_buckets_1553_, v___x_1569_, v___x_1574_);
                    v___x_1576_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1577_ = lean_nat_mul(v_size_x27_1573_, v___x_1576_);
                    v___x_1578_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1579_ = lean_nat_div(v___x_1577_, v___x_1578_);
                    leanh::lean_dec(v___x_1577_);
                    v___x_1580_ = lean_array_get_size(v_buckets_x27_1575_);
                    v___x_1581_ = lean_nat_dec_le(v___x_1579_, v___x_1580_);
                    leanh::lean_dec(v___x_1579_);
                    if v___x_1581_ == 0 {
                        v_val_1582_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1575_);
                        if v_isShared_1556_ == 0 {
                            leanh::lean_ctor_set(v___x_1555_, 1, v_val_1582_);
                            leanh::lean_ctor_set(v___x_1555_, 0, v_size_x27_1573_);
                            v___x_1584_ = v___x_1555_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1585_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1585_,
                                0,
                                v_size_x27_1573_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_val_1582_);
                            v___x_1584_ = v_reuseFailAlloc_1585_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1556_ == 0 {
                            leanh::lean_ctor_set(v___x_1555_, 1, v_buckets_x27_1575_);
                            leanh::lean_ctor_set(v___x_1555_, 0, v_size_x27_1573_);
                            v___x_1587_ = v___x_1555_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1588_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1588_,
                                0,
                                v_size_x27_1573_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1588_,
                                1,
                                v_buckets_x27_1575_,
                            );
                            v___x_1587_ = v_reuseFailAlloc_1588_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1570_);
                    v___x_1589_ = leanh::lean_box(0);
                    v_buckets_x27_1590_ =
                        lean_array_uset(v_buckets_1553_, v___x_1569_, v___x_1589_);
                    v___x_1591_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1550_, v_b_1551_, v_bkt_1570_);
                    v___x_1592_ = lean_array_uset(v_buckets_x27_1590_, v___x_1569_, v___x_1591_);
                    if v_isShared_1556_ == 0 {
                        leanh::lean_ctor_set(v___x_1555_, 1, v___x_1592_);
                        v___x_1594_ = v___x_1555_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_size_1552_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1592_);
                        v___x_1594_ = v_reuseFailAlloc_1595_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1584_;
            }
            3 => {
                return v___x_1587_;
            }
            4 => {
                return v___x_1594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(
    mut v_a_1597_: *mut leanh::LeanObject,
    mut v_e_1598_: *mut leanh::LeanObject,
    mut v_a_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = lean_st_ref_take(v_a_1597_);
    v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v___x_1601_, v_e_1598_, v_a_1599_);
    v___x_1603_ = lean_st_ref_set(v_a_1597_, v___x_1602_);
    v___x_1604_ = leanh::lean_box(0);
    return v___x_1604_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed(
    mut v_a_1605_: *mut leanh::LeanObject,
    mut v_e_1606_: *mut leanh::LeanObject,
    mut v_a_1607_: *mut leanh::LeanObject,
    mut v___y_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(v_a_1605_, v_e_1606_, v_a_1607_);
    leanh::lean_dec(v_a_1605_);
    return v_res_1609_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(
    mut v_00_u03b1_1610_: *mut leanh::LeanObject,
    mut v_x_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = leanh::lean_apply_1(v_x_1611_, leanh::lean_box(0));
    v___x_1618_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1618_, 0, v___x_1617_);
    return v___x_1618_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_1619_: *mut leanh::LeanObject,
    mut v_x_1620_: *mut leanh::LeanObject,
    mut v___y_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
    mut v___y_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(v_00_u03b1_1619_, v_x_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
    leanh::lean_dec(v___y_1624_);
    leanh::lean_dec_ref(v___y_1623_);
    leanh::lean_dec(v___y_1622_);
    leanh::lean_dec_ref(v___y_1621_);
    return v_res_1626_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = leanh::lean_box(0);
    v___x_1628_ = l_Lean_interruptExceptionId;
    v___x_1629_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1629_, 0, v___x_1628_);
    leanh::lean_ctor_set(v___x_1629_, 1, v___x_1627_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
    v___x_1632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1632_, 0, v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___boxed(
    mut v___y_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
    return v_res_1634_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1641_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1641_, 0, v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
    v___x_1643_ = l_Lean_MessageData_ofFormat(v___x_1642_);
    return v___x_1643_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
    v___x_1645_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2;
    v___x_1646_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1646_, 0, v___x_1645_);
    leanh::lean_ctor_set(v___x_1646_, 1, v___x_1644_);
    return v___x_1646_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_ref_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1649_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_1650_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1650_, 0, v_ref_1647_);
    leanh::lean_ctor_set(v___x_1650_, 1, v___x_1649_);
    v___x_1651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1651_, 0, v___x_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_ref_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1654_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1652_);
    return v_res_1654_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(
    mut v_x_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut v___y_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: u8 = 0;
    let mut v___y_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1688_: u8 = 0;
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1705_: u8 = 0;
    let mut v_cancelTk_x3f_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1707_: u8 = 0;
    let mut v_inheritedTraceOptions_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: u8 = 0;
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1720_: u8 = 0;
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1693_ = leanh::lean_ctor_get(v___y_1659_, 0);
                v_fileMap_1694_ = leanh::lean_ctor_get(v___y_1659_, 1);
                v_options_1695_ = leanh::lean_ctor_get(v___y_1659_, 2);
                v_currRecDepth_1696_ = leanh::lean_ctor_get(v___y_1659_, 3);
                v_maxRecDepth_1697_ = leanh::lean_ctor_get(v___y_1659_, 4);
                v_ref_1698_ = leanh::lean_ctor_get(v___y_1659_, 5);
                v_currNamespace_1699_ = leanh::lean_ctor_get(v___y_1659_, 6);
                v_openDecls_1700_ = leanh::lean_ctor_get(v___y_1659_, 7);
                v_initHeartbeats_1701_ = leanh::lean_ctor_get(v___y_1659_, 8);
                v_maxHeartbeats_1702_ = leanh::lean_ctor_get(v___y_1659_, 9);
                v_quotContext_1703_ = leanh::lean_ctor_get(v___y_1659_, 10);
                v_currMacroScope_1704_ = leanh::lean_ctor_get(v___y_1659_, 11);
                v_diag_1705_ = leanh::lean_ctor_get_uint8(
                    v___y_1659_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1706_ = leanh::lean_ctor_get(v___y_1659_, 12);
                v_suppressElabErrors_1707_ = leanh::lean_ctor_get_uint8(
                    v___y_1659_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1708_ = leanh::lean_ctor_get(v___y_1659_, 13);
                if leanh::lean_obj_tag(v_cancelTk_x3f_1706_) == 1 {
                    v_val_1714_ = leanh::lean_ctor_get(v_cancelTk_x3f_1706_, 0);
                    v___x_1715_ = l_IO_CancelToken_isSet(v_val_1714_);
                    if v___x_1715_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_1655_);
                        v___x_1716_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_1717_ = leanh::lean_ctor_get(v___x_1716_, 0);
                        v_isSharedCheck_1724_ =
                            (!leanh::lean_is_exclusive(v___x_1716_)) as u8;
                        if v_isSharedCheck_1724_ == 0 {
                            v___x_1719_ = v___x_1716_;
                            v_isShared_1720_ = v_isSharedCheck_1724_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1717_);
                            leanh::lean_dec(v___x_1716_);
                            v___x_1719_ = leanh::lean_box(0);
                            v_isShared_1720_ = v_isSharedCheck_1724_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1663_) == 0 {
                    return v___y_1663_;
                } else {
                    v_a_1664_ = leanh::lean_ctor_get(v___y_1663_, 0);
                    v_isSharedCheck_1671_ = (!leanh::lean_is_exclusive(v___y_1663_)) as u8;
                    if v_isSharedCheck_1671_ == 0 {
                        v___x_1666_ = v___y_1663_;
                        v_isShared_1667_ = v_isSharedCheck_1671_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1664_);
                        leanh::lean_dec(v___y_1663_);
                        v___x_1666_ = leanh::lean_box(0);
                        v_isShared_1667_ = v_isSharedCheck_1671_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1667_ == 0 {
                    v___x_1669_ = v___x_1666_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1670_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
                    v___x_1669_ = v_reuseFailAlloc_1670_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1669_;
            }
            4 => {
                v___x_1689_ = leanh::lean_unsigned_to_nat(1);
                v___x_1690_ = lean_nat_add(v___y_1679_, v___x_1689_);
                leanh::lean_inc_ref(v___y_1673_);
                leanh::lean_inc(v___y_1682_);
                leanh::lean_inc(v___y_1686_);
                leanh::lean_inc(v___y_1681_);
                leanh::lean_inc(v___y_1684_);
                leanh::lean_inc(v___y_1678_);
                leanh::lean_inc(v___y_1677_);
                leanh::lean_inc(v___y_1687_);
                leanh::lean_inc(v___y_1674_);
                leanh::lean_inc_ref(v___y_1685_);
                leanh::lean_inc_ref(v___y_1676_);
                leanh::lean_inc_ref(v___y_1680_);
                v___x_1691_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_1691_, 0, v___y_1680_);
                leanh::lean_ctor_set(v___x_1691_, 1, v___y_1676_);
                leanh::lean_ctor_set(v___x_1691_, 2, v___y_1685_);
                leanh::lean_ctor_set(v___x_1691_, 3, v___x_1690_);
                leanh::lean_ctor_set(v___x_1691_, 4, v___y_1674_);
                leanh::lean_ctor_set(v___x_1691_, 5, v___y_1675_);
                leanh::lean_ctor_set(v___x_1691_, 6, v___y_1687_);
                leanh::lean_ctor_set(v___x_1691_, 7, v___y_1677_);
                leanh::lean_ctor_set(v___x_1691_, 8, v___y_1678_);
                leanh::lean_ctor_set(v___x_1691_, 9, v___y_1684_);
                leanh::lean_ctor_set(v___x_1691_, 10, v___y_1681_);
                leanh::lean_ctor_set(v___x_1691_, 11, v___y_1686_);
                leanh::lean_ctor_set(v___x_1691_, 12, v___y_1682_);
                leanh::lean_ctor_set(v___x_1691_, 13, v___y_1673_);
                leanh::lean_ctor_set_uint8(
                    v___x_1691_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_1683_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1691_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_1688_,
                );
                leanh::lean_inc(v___y_1660_);
                leanh::lean_inc(v___y_1658_);
                leanh::lean_inc_ref(v___y_1657_);
                leanh::lean_inc(v___y_1656_);
                v___x_1692_ = leanh::lean_apply_6(
                    v_x_1655_,
                    v___y_1656_,
                    v___y_1657_,
                    v___y_1658_,
                    v___x_1691_,
                    v___y_1660_,
                    leanh::lean_box(0),
                );
                v___y_1663_ = v___x_1692_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1710_ = leanh::lean_unsigned_to_nat(0);
                v___x_1711_ = lean_nat_dec_eq(v_maxRecDepth_1697_, v___x_1710_);
                if v___x_1711_ == 0 {
                    v___x_1712_ = lean_nat_dec_eq(v_currRecDepth_1696_, v_maxRecDepth_1697_);
                    if v___x_1712_ == 0 {
                        leanh::lean_inc(v_ref_1698_);
                        v___y_1673_ = v_inheritedTraceOptions_1708_;
                        v___y_1674_ = v_maxRecDepth_1697_;
                        v___y_1675_ = v_ref_1698_;
                        v___y_1676_ = v_fileMap_1694_;
                        v___y_1677_ = v_openDecls_1700_;
                        v___y_1678_ = v_initHeartbeats_1701_;
                        v___y_1679_ = v_currRecDepth_1696_;
                        v___y_1680_ = v_fileName_1693_;
                        v___y_1681_ = v_quotContext_1703_;
                        v___y_1682_ = v_cancelTk_x3f_1706_;
                        v___y_1683_ = v_diag_1705_;
                        v___y_1684_ = v_maxHeartbeats_1702_;
                        v___y_1685_ = v_options_1695_;
                        v___y_1686_ = v_currMacroScope_1704_;
                        v___y_1687_ = v_currNamespace_1699_;
                        v___y_1688_ = v_suppressElabErrors_1707_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_1655_);
                        leanh::lean_inc(v_ref_1698_);
                        v___x_1713_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1698_);
                        v___y_1663_ = v___x_1713_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_ref_1698_);
                    v___y_1673_ = v_inheritedTraceOptions_1708_;
                    v___y_1674_ = v_maxRecDepth_1697_;
                    v___y_1675_ = v_ref_1698_;
                    v___y_1676_ = v_fileMap_1694_;
                    v___y_1677_ = v_openDecls_1700_;
                    v___y_1678_ = v_initHeartbeats_1701_;
                    v___y_1679_ = v_currRecDepth_1696_;
                    v___y_1680_ = v_fileName_1693_;
                    v___y_1681_ = v_quotContext_1703_;
                    v___y_1682_ = v_cancelTk_x3f_1706_;
                    v___y_1683_ = v_diag_1705_;
                    v___y_1684_ = v_maxHeartbeats_1702_;
                    v___y_1685_ = v_options_1695_;
                    v___y_1686_ = v_currMacroScope_1704_;
                    v___y_1687_ = v_currNamespace_1699_;
                    v___y_1688_ = v_suppressElabErrors_1707_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_1720_ == 0 {
                    v___x_1722_ = v___x_1719_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
                    v___x_1722_ = v_reuseFailAlloc_1723_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg___boxed(
    mut v_x_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
    mut v___y_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
    leanh::lean_dec(v___y_1730_);
    leanh::lean_dec_ref(v___y_1729_);
    leanh::lean_dec(v___y_1728_);
    leanh::lean_dec_ref(v___y_1727_);
    leanh::lean_dec(v___y_1726_);
    return v_res_1732_;
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = leanh::lean_box(0);
    v_dummy_1735_ = l_Lean_Expr_sort___override(v___x_1734_);
    return v_dummy_1735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(
    mut v_pre_1736_: *mut leanh::LeanObject,
    mut v_post_1737_: *mut leanh::LeanObject,
    mut v_sz_1738_: usize,
    mut v_i_1739_: usize,
    mut v_bs_1740_: *mut leanh::LeanObject,
    mut v___y_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
    mut v___y_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1747_: u8 = 0;
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: usize = 0;
    let mut v___x_1755_: usize = 0;
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1747_ = lean_usize_dec_lt(v_i_1739_, v_sz_1738_);
                if v___x_1747_ == 0 {
                    leanh::lean_dec_ref(v_post_1737_);
                    leanh::lean_dec_ref(v_pre_1736_);
                    v___x_1748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1748_, 0, v_bs_1740_);
                    return v___x_1748_;
                } else {
                    v_v_1749_ = lean_array_uget_borrowed(v_bs_1740_, v_i_1739_);
                    leanh::lean_inc(v_v_1749_);
                    leanh::lean_inc_ref(v_post_1737_);
                    leanh::lean_inc_ref(v_pre_1736_);
                    v___x_1750_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1736_, v_post_1737_, v_v_1749_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
                    if leanh::lean_obj_tag(v___x_1750_) == 0 {
                        v_a_1751_ = leanh::lean_ctor_get(v___x_1750_, 0);
                        leanh::lean_inc(v_a_1751_);
                        leanh::lean_dec_ref_known(v___x_1750_, 1);
                        v___x_1752_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1753_ = lean_array_uset(v_bs_1740_, v_i_1739_, v___x_1752_);
                        v___x_1754_ = 1usize;
                        v___x_1755_ = lean_usize_add(v_i_1739_, v___x_1754_);
                        v___x_1756_ = lean_array_uset(v_bs_x27_1753_, v_i_1739_, v_a_1751_);
                        v_i_1739_ = v___x_1755_;
                        v_bs_1740_ = v___x_1756_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_1740_);
                        leanh::lean_dec_ref(v_post_1737_);
                        leanh::lean_dec_ref(v_pre_1736_);
                        v_a_1758_ = leanh::lean_ctor_get(v___x_1750_, 0);
                        v_isSharedCheck_1765_ =
                            (!leanh::lean_is_exclusive(v___x_1750_)) as u8;
                        if v_isSharedCheck_1765_ == 0 {
                            v___x_1760_ = v___x_1750_;
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1758_);
                            leanh::lean_dec(v___x_1750_);
                            v___x_1760_ = leanh::lean_box(0);
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1761_ == 0 {
                    v___x_1763_ = v___x_1760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1764_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
                    v___x_1763_ = v_reuseFailAlloc_1764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1763_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(
    mut v_pre_1766_: *mut leanh::LeanObject,
    mut v_post_1767_: *mut leanh::LeanObject,
    mut v_x_1768_: *mut leanh::LeanObject,
    mut v_x_1769_: *mut leanh::LeanObject,
    mut v_x_1770_: *mut leanh::LeanObject,
    mut v___y_1771_: *mut leanh::LeanObject,
    mut v___y_1772_: *mut leanh::LeanObject,
    mut v___y_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1768_) == 5 {
                    v_fn_1777_ = leanh::lean_ctor_get(v_x_1768_, 0);
                    leanh::lean_inc_ref(v_fn_1777_);
                    v_arg_1778_ = leanh::lean_ctor_get(v_x_1768_, 1);
                    leanh::lean_inc_ref(v_arg_1778_);
                    leanh::lean_dec_ref_known(v_x_1768_, 2);
                    v___x_1779_ = lean_array_set(v_x_1769_, v_x_1770_, v_arg_1778_);
                    v___x_1780_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1781_ = lean_nat_sub(v_x_1770_, v___x_1780_);
                    leanh::lean_dec(v_x_1770_);
                    v_x_1768_ = v_fn_1777_;
                    v_x_1769_ = v___x_1779_;
                    v_x_1770_ = v___x_1781_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_1770_);
                    leanh::lean_inc_ref(v_post_1767_);
                    leanh::lean_inc_ref(v_pre_1766_);
                    v___x_1783_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1766_, v_post_1767_, v_x_1768_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
                    if leanh::lean_obj_tag(v___x_1783_) == 0 {
                        v_a_1784_ = leanh::lean_ctor_get(v___x_1783_, 0);
                        leanh::lean_inc(v_a_1784_);
                        leanh::lean_dec_ref_known(v___x_1783_, 1);
                        v_sz_1785_ = lean_array_size(v_x_1769_);
                        v___x_1786_ = 0usize;
                        leanh::lean_inc_ref(v_post_1767_);
                        leanh::lean_inc_ref(v_pre_1766_);
                        v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_1766_, v_post_1767_, v_sz_1785_, v___x_1786_, v_x_1769_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
                        if leanh::lean_obj_tag(v___x_1787_) == 0 {
                            v_a_1788_ = leanh::lean_ctor_get(v___x_1787_, 0);
                            leanh::lean_inc(v_a_1788_);
                            leanh::lean_dec_ref_known(v___x_1787_, 1);
                            v___x_1789_ = l_Lean_mkAppN(v_a_1784_, v_a_1788_);
                            leanh::lean_dec(v_a_1788_);
                            v___x_1790_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1766_, v_post_1767_, v___x_1789_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
                            return v___x_1790_;
                        } else {
                            leanh::lean_dec(v_a_1784_);
                            leanh::lean_dec_ref(v_post_1767_);
                            leanh::lean_dec_ref(v_pre_1766_);
                            v_a_1791_ = leanh::lean_ctor_get(v___x_1787_, 0);
                            v_isSharedCheck_1798_ =
                                (!leanh::lean_is_exclusive(v___x_1787_)) as u8;
                            if v_isSharedCheck_1798_ == 0 {
                                v___x_1793_ = v___x_1787_;
                                v_isShared_1794_ = v_isSharedCheck_1798_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1791_);
                                leanh::lean_dec(v___x_1787_);
                                v___x_1793_ = leanh::lean_box(0);
                                v_isShared_1794_ = v_isSharedCheck_1798_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_1769_);
                        leanh::lean_dec_ref(v_post_1767_);
                        leanh::lean_dec_ref(v_pre_1766_);
                        return v___x_1783_;
                    }
                }
            }
            1 => {
                if v_isShared_1794_ == 0 {
                    v___x_1796_ = v___x_1793_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1797_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
                    v___x_1796_ = v_reuseFailAlloc_1797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(
    mut v___x_1799_: *mut leanh::LeanObject,
    mut v_pre_1800_: *mut leanh::LeanObject,
    mut v_e_1801_: *mut leanh::LeanObject,
    mut v_post_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1810_: u8 = 0;
    let mut v___y_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1817_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: usize = 0;
    let mut v___x_1821_: usize = 0;
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1827_: u8 = 0;
    let mut v___y_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1843_: u8 = 0;
    let mut v___y_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1845_: u8 = 0;
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1857_: u8 = 0;
    let mut v___y_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1863_: u8 = 0;
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: usize = 0;
    let mut v___x_1869_: usize = 0;
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: usize = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: u8 = 0;
    let mut v_binderName_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1877_: u8 = 0;
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: usize = 0;
    let mut v___x_1884_: u8 = 0;
    let mut v___x_1885_: usize = 0;
    let mut v___x_1886_: usize = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v_declName_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1892_: u8 = 0;
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: usize = 0;
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: usize = 0;
    let mut v___x_1903_: usize = 0;
    let mut v___x_1904_: u8 = 0;
    let mut v_dummy_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: usize = 0;
    let mut v___x_1916_: usize = 0;
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: usize = 0;
    let mut v___x_1927_: usize = 0;
    let mut v___x_1928_: u8 = 0;
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_a_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v_a_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1852_ = l_Lean_Core_checkSystem(v___x_1799_, v___y_1806_, v___y_1807_);
                if leanh::lean_obj_tag(v___x_1852_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1852_, 1);
                    leanh::lean_inc_ref(v_pre_1800_);
                    leanh::lean_inc(v___y_1807_);
                    leanh::lean_inc_ref(v___y_1806_);
                    leanh::lean_inc(v___y_1805_);
                    leanh::lean_inc_ref(v___y_1804_);
                    leanh::lean_inc_ref(v_e_1801_);
                    v___x_1853_ = leanh::lean_apply_6(
                        v_pre_1800_,
                        v_e_1801_,
                        v___y_1804_,
                        v___y_1805_,
                        v___y_1806_,
                        v___y_1807_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1853_) == 0 {
                        v_a_1854_ = leanh::lean_ctor_get(v___x_1853_, 0);
                        v_isSharedCheck_1943_ =
                            (!leanh::lean_is_exclusive(v___x_1853_)) as u8;
                        if v_isSharedCheck_1943_ == 0 {
                            v___x_1856_ = v___x_1853_;
                            v_isShared_1857_ = v_isSharedCheck_1943_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1854_);
                            leanh::lean_dec(v___x_1853_);
                            v___x_1856_ = leanh::lean_box(0);
                            v_isShared_1857_ = v_isSharedCheck_1943_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_1802_);
                        leanh::lean_dec_ref(v_e_1801_);
                        leanh::lean_dec_ref(v_pre_1800_);
                        v_a_1944_ = leanh::lean_ctor_get(v___x_1853_, 0);
                        v_isSharedCheck_1951_ =
                            (!leanh::lean_is_exclusive(v___x_1853_)) as u8;
                        if v_isSharedCheck_1951_ == 0 {
                            v___x_1946_ = v___x_1853_;
                            v_isShared_1947_ = v_isSharedCheck_1951_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1944_);
                            leanh::lean_dec(v___x_1853_);
                            v___x_1946_ = leanh::lean_box(0);
                            v_isShared_1947_ = v_isSharedCheck_1951_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_1802_);
                    leanh::lean_dec_ref(v_e_1801_);
                    leanh::lean_dec_ref(v_pre_1800_);
                    v_a_1952_ = leanh::lean_ctor_get(v___x_1852_, 0);
                    v_isSharedCheck_1959_ = (!leanh::lean_is_exclusive(v___x_1852_)) as u8;
                    if v_isSharedCheck_1959_ == 0 {
                        v___x_1954_ = v___x_1852_;
                        v_isShared_1955_ = v_isSharedCheck_1959_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1952_);
                        leanh::lean_dec(v___x_1852_);
                        v___x_1954_ = leanh::lean_box(0);
                        v_isShared_1955_ = v_isSharedCheck_1959_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1817_ == 0 {
                    leanh::lean_dec_ref(v___y_1816_);
                    leanh::lean_dec_ref(v___y_1815_);
                    v___x_1818_ = l_Lean_Expr_letE___override(
                        v___y_1813_,
                        v___y_1811_,
                        v___y_1814_,
                        v___y_1812_,
                        v___y_1810_,
                    );
                    v___x_1819_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1818_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    return v___x_1819_;
                } else {
                    v___x_1820_ = lean_ptr_addr(v___y_1815_);
                    leanh::lean_dec_ref(v___y_1815_);
                    v___x_1821_ = lean_ptr_addr(v___y_1812_);
                    v___x_1822_ = lean_usize_dec_eq(v___x_1820_, v___x_1821_);
                    if v___x_1822_ == 0 {
                        leanh::lean_dec_ref(v___y_1816_);
                        v___x_1823_ = l_Lean_Expr_letE___override(
                            v___y_1813_,
                            v___y_1811_,
                            v___y_1814_,
                            v___y_1812_,
                            v___y_1810_,
                        );
                        v___x_1824_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1823_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        return v___x_1824_;
                    } else {
                        leanh::lean_dec_ref(v___y_1814_);
                        leanh::lean_dec(v___y_1813_);
                        leanh::lean_dec_ref(v___y_1812_);
                        leanh::lean_dec_ref(v___y_1811_);
                        v___x_1825_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___y_1816_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        return v___x_1825_;
                    }
                }
            }
            2 => {
                if v___y_1832_ == 0 {
                    leanh::lean_dec_ref(v___y_1831_);
                    v___x_1833_ = l_Lean_Expr_lam___override(
                        v___y_1830_,
                        v___y_1828_,
                        v___y_1829_,
                        v___y_1827_,
                    );
                    v___x_1834_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1833_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    return v___x_1834_;
                } else {
                    v___x_1835_ = l_Lean_instBEqBinderInfo_beq(v___y_1827_, v___y_1827_);
                    if v___x_1835_ == 0 {
                        leanh::lean_dec_ref(v___y_1831_);
                        v___x_1836_ = l_Lean_Expr_lam___override(
                            v___y_1830_,
                            v___y_1828_,
                            v___y_1829_,
                            v___y_1827_,
                        );
                        v___x_1837_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1836_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        return v___x_1837_;
                    } else {
                        leanh::lean_dec(v___y_1830_);
                        leanh::lean_dec_ref(v___y_1829_);
                        leanh::lean_dec_ref(v___y_1828_);
                        v___x_1838_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___y_1831_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        return v___x_1838_;
                    }
                }
            }
            3 => {
                if v___y_1845_ == 0 {
                    leanh::lean_dec_ref(v___y_1844_);
                    v___x_1846_ = l_Lean_Expr_forallE___override(
                        v___y_1841_,
                        v___y_1842_,
                        v___y_1840_,
                        v___y_1843_,
                    );
                    v___x_1847_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1846_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    return v___x_1847_;
                } else {
                    v___x_1848_ = l_Lean_instBEqBinderInfo_beq(v___y_1843_, v___y_1843_);
                    if v___x_1848_ == 0 {
                        leanh::lean_dec_ref(v___y_1844_);
                        v___x_1849_ = l_Lean_Expr_forallE___override(
                            v___y_1841_,
                            v___y_1842_,
                            v___y_1840_,
                            v___y_1843_,
                        );
                        v___x_1850_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1849_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        return v___x_1850_;
                    } else {
                        leanh::lean_dec_ref(v___y_1842_);
                        leanh::lean_dec(v___y_1841_);
                        leanh::lean_dec_ref(v___y_1840_);
                        v___x_1851_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___y_1844_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        return v___x_1851_;
                    }
                }
            }
            4 => match leanh::lean_obj_tag(v_a_1854_) {
                0 => {
                    leanh::lean_dec_ref(v_post_1802_);
                    leanh::lean_dec_ref(v_e_1801_);
                    leanh::lean_dec_ref(v_pre_1800_);
                    v_e_1933_ = leanh::lean_ctor_get(v_a_1854_, 0);
                    leanh::lean_inc_ref(v_e_1933_);
                    leanh::lean_dec_ref_known(v_a_1854_, 1);
                    if v_isShared_1857_ == 0 {
                        leanh::lean_ctor_set(v___x_1856_, 0, v_e_1933_);
                        v___x_1935_ = v___x_1856_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1936_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_e_1933_);
                        v___x_1935_ = v_reuseFailAlloc_1936_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_1856_);
                    leanh::lean_dec_ref(v_e_1801_);
                    v_e_1937_ = leanh::lean_ctor_get(v_a_1854_, 0);
                    leanh::lean_inc_ref(v_e_1937_);
                    leanh::lean_dec_ref_known(v_a_1854_, 1);
                    leanh::lean_inc_ref(v_post_1802_);
                    leanh::lean_inc_ref(v_pre_1800_);
                    v___x_1938_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_e_1937_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    if leanh::lean_obj_tag(v___x_1938_) == 0 {
                        v_a_1939_ = leanh::lean_ctor_get(v___x_1938_, 0);
                        leanh::lean_inc(v_a_1939_);
                        leanh::lean_dec_ref_known(v___x_1938_, 1);
                        v___x_1940_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v_a_1939_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        return v___x_1940_;
                    } else {
                        leanh::lean_dec_ref(v_post_1802_);
                        leanh::lean_dec_ref(v_pre_1800_);
                        return v___x_1938_;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_1856_);
                    v_e_x3f_1941_ = leanh::lean_ctor_get(v_a_1854_, 0);
                    leanh::lean_inc(v_e_x3f_1941_);
                    leanh::lean_dec_ref_known(v_a_1854_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_1941_) == 0 {
                        v___y_1859_ = v_e_1801_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_1801_);
                        v_val_1942_ = leanh::lean_ctor_get(v_e_x3f_1941_, 0);
                        leanh::lean_inc(v_val_1942_);
                        leanh::lean_dec_ref_known(v_e_x3f_1941_, 1);
                        v___y_1859_ = v_val_1942_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match leanh::lean_obj_tag(v___y_1859_) {
                7 => {
                    v_binderName_1860_ = leanh::lean_ctor_get(v___y_1859_, 0);
                    leanh::lean_inc(v_binderName_1860_);
                    v_binderType_1861_ = leanh::lean_ctor_get(v___y_1859_, 1);
                    v_body_1862_ = leanh::lean_ctor_get(v___y_1859_, 2);
                    v_binderInfo_1863_ = leanh::lean_ctor_get_uint8(
                        v___y_1859_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_1861_);
                    leanh::lean_inc_ref(v_post_1802_);
                    leanh::lean_inc_ref(v_pre_1800_);
                    v___x_1864_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_binderType_1861_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    if leanh::lean_obj_tag(v___x_1864_) == 0 {
                        v_a_1865_ = leanh::lean_ctor_get(v___x_1864_, 0);
                        leanh::lean_inc(v_a_1865_);
                        leanh::lean_dec_ref_known(v___x_1864_, 1);
                        leanh::lean_inc_ref(v_body_1862_);
                        leanh::lean_inc_ref(v_post_1802_);
                        leanh::lean_inc_ref(v_pre_1800_);
                        v___x_1866_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_body_1862_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        if leanh::lean_obj_tag(v___x_1866_) == 0 {
                            v_a_1867_ = leanh::lean_ctor_get(v___x_1866_, 0);
                            leanh::lean_inc(v_a_1867_);
                            leanh::lean_dec_ref_known(v___x_1866_, 1);
                            v___x_1868_ = lean_ptr_addr(v_binderType_1861_);
                            v___x_1869_ = lean_ptr_addr(v_a_1865_);
                            v___x_1870_ = lean_usize_dec_eq(v___x_1868_, v___x_1869_);
                            if v___x_1870_ == 0 {
                                v___y_1840_ = v_a_1867_;
                                v___y_1841_ = v_binderName_1860_;
                                v___y_1842_ = v_a_1865_;
                                v___y_1843_ = v_binderInfo_1863_;
                                v___y_1844_ = v___y_1859_;
                                v___y_1845_ = v___x_1870_;
                                state = 3;
                                continue;
                            } else {
                                v___x_1871_ = lean_ptr_addr(v_body_1862_);
                                v___x_1872_ = lean_ptr_addr(v_a_1867_);
                                v___x_1873_ = lean_usize_dec_eq(v___x_1871_, v___x_1872_);
                                v___y_1840_ = v_a_1867_;
                                v___y_1841_ = v_binderName_1860_;
                                v___y_1842_ = v_a_1865_;
                                v___y_1843_ = v_binderInfo_1863_;
                                v___y_1844_ = v___y_1859_;
                                v___y_1845_ = v___x_1873_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1865_);
                            leanh::lean_dec_ref_known(v___y_1859_, 3);
                            leanh::lean_dec(v_binderName_1860_);
                            leanh::lean_dec_ref(v_post_1802_);
                            leanh::lean_dec_ref(v_pre_1800_);
                            return v___x_1866_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1859_, 3);
                        leanh::lean_dec(v_binderName_1860_);
                        leanh::lean_dec_ref(v_post_1802_);
                        leanh::lean_dec_ref(v_pre_1800_);
                        return v___x_1864_;
                    }
                }
                6 => {
                    v_binderName_1874_ = leanh::lean_ctor_get(v___y_1859_, 0);
                    leanh::lean_inc(v_binderName_1874_);
                    v_binderType_1875_ = leanh::lean_ctor_get(v___y_1859_, 1);
                    v_body_1876_ = leanh::lean_ctor_get(v___y_1859_, 2);
                    v_binderInfo_1877_ = leanh::lean_ctor_get_uint8(
                        v___y_1859_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_1875_);
                    leanh::lean_inc_ref(v_post_1802_);
                    leanh::lean_inc_ref(v_pre_1800_);
                    v___x_1878_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_binderType_1875_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    if leanh::lean_obj_tag(v___x_1878_) == 0 {
                        v_a_1879_ = leanh::lean_ctor_get(v___x_1878_, 0);
                        leanh::lean_inc(v_a_1879_);
                        leanh::lean_dec_ref_known(v___x_1878_, 1);
                        leanh::lean_inc_ref(v_body_1876_);
                        leanh::lean_inc_ref(v_post_1802_);
                        leanh::lean_inc_ref(v_pre_1800_);
                        v___x_1880_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_body_1876_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        if leanh::lean_obj_tag(v___x_1880_) == 0 {
                            v_a_1881_ = leanh::lean_ctor_get(v___x_1880_, 0);
                            leanh::lean_inc(v_a_1881_);
                            leanh::lean_dec_ref_known(v___x_1880_, 1);
                            v___x_1882_ = lean_ptr_addr(v_binderType_1875_);
                            v___x_1883_ = lean_ptr_addr(v_a_1879_);
                            v___x_1884_ = lean_usize_dec_eq(v___x_1882_, v___x_1883_);
                            if v___x_1884_ == 0 {
                                v___y_1827_ = v_binderInfo_1877_;
                                v___y_1828_ = v_a_1879_;
                                v___y_1829_ = v_a_1881_;
                                v___y_1830_ = v_binderName_1874_;
                                v___y_1831_ = v___y_1859_;
                                v___y_1832_ = v___x_1884_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1885_ = lean_ptr_addr(v_body_1876_);
                                v___x_1886_ = lean_ptr_addr(v_a_1881_);
                                v___x_1887_ = lean_usize_dec_eq(v___x_1885_, v___x_1886_);
                                v___y_1827_ = v_binderInfo_1877_;
                                v___y_1828_ = v_a_1879_;
                                v___y_1829_ = v_a_1881_;
                                v___y_1830_ = v_binderName_1874_;
                                v___y_1831_ = v___y_1859_;
                                v___y_1832_ = v___x_1887_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1879_);
                            leanh::lean_dec_ref_known(v___y_1859_, 3);
                            leanh::lean_dec(v_binderName_1874_);
                            leanh::lean_dec_ref(v_post_1802_);
                            leanh::lean_dec_ref(v_pre_1800_);
                            return v___x_1880_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1859_, 3);
                        leanh::lean_dec(v_binderName_1874_);
                        leanh::lean_dec_ref(v_post_1802_);
                        leanh::lean_dec_ref(v_pre_1800_);
                        return v___x_1878_;
                    }
                }
                8 => {
                    v_declName_1888_ = leanh::lean_ctor_get(v___y_1859_, 0);
                    leanh::lean_inc(v_declName_1888_);
                    v_type_1889_ = leanh::lean_ctor_get(v___y_1859_, 1);
                    v_value_1890_ = leanh::lean_ctor_get(v___y_1859_, 2);
                    v_body_1891_ = leanh::lean_ctor_get(v___y_1859_, 3);
                    leanh::lean_inc_ref(v_body_1891_);
                    v_nondep_1892_ = leanh::lean_ctor_get_uint8(
                        v___y_1859_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_type_1889_);
                    leanh::lean_inc_ref(v_post_1802_);
                    leanh::lean_inc_ref(v_pre_1800_);
                    v___x_1893_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_type_1889_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    if leanh::lean_obj_tag(v___x_1893_) == 0 {
                        v_a_1894_ = leanh::lean_ctor_get(v___x_1893_, 0);
                        leanh::lean_inc(v_a_1894_);
                        leanh::lean_dec_ref_known(v___x_1893_, 1);
                        leanh::lean_inc_ref(v_value_1890_);
                        leanh::lean_inc_ref(v_post_1802_);
                        leanh::lean_inc_ref(v_pre_1800_);
                        v___x_1895_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_value_1890_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                        if leanh::lean_obj_tag(v___x_1895_) == 0 {
                            v_a_1896_ = leanh::lean_ctor_get(v___x_1895_, 0);
                            leanh::lean_inc(v_a_1896_);
                            leanh::lean_dec_ref_known(v___x_1895_, 1);
                            leanh::lean_inc_ref(v_body_1891_);
                            leanh::lean_inc_ref(v_post_1802_);
                            leanh::lean_inc_ref(v_pre_1800_);
                            v___x_1897_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_body_1891_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                            if leanh::lean_obj_tag(v___x_1897_) == 0 {
                                v_a_1898_ = leanh::lean_ctor_get(v___x_1897_, 0);
                                leanh::lean_inc(v_a_1898_);
                                leanh::lean_dec_ref_known(v___x_1897_, 1);
                                v___x_1899_ = lean_ptr_addr(v_type_1889_);
                                v___x_1900_ = lean_ptr_addr(v_a_1894_);
                                v___x_1901_ = lean_usize_dec_eq(v___x_1899_, v___x_1900_);
                                if v___x_1901_ == 0 {
                                    v___y_1810_ = v_nondep_1892_;
                                    v___y_1811_ = v_a_1894_;
                                    v___y_1812_ = v_a_1898_;
                                    v___y_1813_ = v_declName_1888_;
                                    v___y_1814_ = v_a_1896_;
                                    v___y_1815_ = v_body_1891_;
                                    v___y_1816_ = v___y_1859_;
                                    v___y_1817_ = v___x_1901_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1902_ = lean_ptr_addr(v_value_1890_);
                                    v___x_1903_ = lean_ptr_addr(v_a_1896_);
                                    v___x_1904_ = lean_usize_dec_eq(v___x_1902_, v___x_1903_);
                                    v___y_1810_ = v_nondep_1892_;
                                    v___y_1811_ = v_a_1894_;
                                    v___y_1812_ = v_a_1898_;
                                    v___y_1813_ = v_declName_1888_;
                                    v___y_1814_ = v_a_1896_;
                                    v___y_1815_ = v_body_1891_;
                                    v___y_1816_ = v___y_1859_;
                                    v___y_1817_ = v___x_1904_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1896_);
                                leanh::lean_dec(v_a_1894_);
                                leanh::lean_dec_ref(v_body_1891_);
                                leanh::lean_dec_ref_known(v___y_1859_, 4);
                                leanh::lean_dec(v_declName_1888_);
                                leanh::lean_dec_ref(v_post_1802_);
                                leanh::lean_dec_ref(v_pre_1800_);
                                return v___x_1897_;
                            }
                        } else {
                            leanh::lean_dec(v_a_1894_);
                            leanh::lean_dec_ref(v_body_1891_);
                            leanh::lean_dec(v_declName_1888_);
                            leanh::lean_dec_ref_known(v___y_1859_, 4);
                            leanh::lean_dec_ref(v_post_1802_);
                            leanh::lean_dec_ref(v_pre_1800_);
                            return v___x_1895_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_1891_);
                        leanh::lean_dec_ref_known(v___y_1859_, 4);
                        leanh::lean_dec(v_declName_1888_);
                        leanh::lean_dec_ref(v_post_1802_);
                        leanh::lean_dec_ref(v_pre_1800_);
                        return v___x_1893_;
                    }
                }
                5 => {
                    v_dummy_1905_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_1906_ = l_Lean_Expr_getAppNumArgs(v___y_1859_);
                    leanh::lean_inc(v_nargs_1906_);
                    v___x_1907_ = lean_mk_array(v_nargs_1906_, v_dummy_1905_);
                    v___x_1908_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1909_ = lean_nat_sub(v_nargs_1906_, v___x_1908_);
                    leanh::lean_dec(v_nargs_1906_);
                    v___x_1910_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_1800_, v_post_1802_, v___y_1859_, v___x_1907_, v___x_1909_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    return v___x_1910_;
                }
                10 => {
                    v_data_1911_ = leanh::lean_ctor_get(v___y_1859_, 0);
                    v_expr_1912_ = leanh::lean_ctor_get(v___y_1859_, 1);
                    leanh::lean_inc_ref(v_expr_1912_);
                    leanh::lean_inc_ref(v_post_1802_);
                    leanh::lean_inc_ref(v_pre_1800_);
                    v___x_1913_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_expr_1912_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    if leanh::lean_obj_tag(v___x_1913_) == 0 {
                        v_a_1914_ = leanh::lean_ctor_get(v___x_1913_, 0);
                        leanh::lean_inc(v_a_1914_);
                        leanh::lean_dec_ref_known(v___x_1913_, 1);
                        v___x_1915_ = lean_ptr_addr(v_expr_1912_);
                        v___x_1916_ = lean_ptr_addr(v_a_1914_);
                        v___x_1917_ = lean_usize_dec_eq(v___x_1915_, v___x_1916_);
                        if v___x_1917_ == 0 {
                            leanh::lean_inc(v_data_1911_);
                            leanh::lean_dec_ref_known(v___y_1859_, 2);
                            v___x_1918_ = l_Lean_Expr_mdata___override(v_data_1911_, v_a_1914_);
                            v___x_1919_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1918_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                            return v___x_1919_;
                        } else {
                            leanh::lean_dec(v_a_1914_);
                            v___x_1920_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___y_1859_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                            return v___x_1920_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1859_, 2);
                        leanh::lean_dec_ref(v_post_1802_);
                        leanh::lean_dec_ref(v_pre_1800_);
                        return v___x_1913_;
                    }
                }
                11 => {
                    v_typeName_1921_ = leanh::lean_ctor_get(v___y_1859_, 0);
                    v_idx_1922_ = leanh::lean_ctor_get(v___y_1859_, 1);
                    v_struct_1923_ = leanh::lean_ctor_get(v___y_1859_, 2);
                    leanh::lean_inc_ref(v_struct_1923_);
                    leanh::lean_inc_ref(v_post_1802_);
                    leanh::lean_inc_ref(v_pre_1800_);
                    v___x_1924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_1800_, v_post_1802_, v_struct_1923_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    if leanh::lean_obj_tag(v___x_1924_) == 0 {
                        v_a_1925_ = leanh::lean_ctor_get(v___x_1924_, 0);
                        leanh::lean_inc(v_a_1925_);
                        leanh::lean_dec_ref_known(v___x_1924_, 1);
                        v___x_1926_ = lean_ptr_addr(v_struct_1923_);
                        v___x_1927_ = lean_ptr_addr(v_a_1925_);
                        v___x_1928_ = lean_usize_dec_eq(v___x_1926_, v___x_1927_);
                        if v___x_1928_ == 0 {
                            leanh::lean_inc(v_idx_1922_);
                            leanh::lean_inc(v_typeName_1921_);
                            leanh::lean_dec_ref_known(v___y_1859_, 3);
                            v___x_1929_ = l_Lean_Expr_proj___override(
                                v_typeName_1921_,
                                v_idx_1922_,
                                v_a_1925_,
                            );
                            v___x_1930_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___x_1929_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                            return v___x_1930_;
                        } else {
                            leanh::lean_dec(v_a_1925_);
                            v___x_1931_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___y_1859_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                            return v___x_1931_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1859_, 3);
                        leanh::lean_dec_ref(v_post_1802_);
                        leanh::lean_dec_ref(v_pre_1800_);
                        return v___x_1924_;
                    }
                }
                _ => {
                    v___x_1932_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_1800_, v_post_1802_, v___y_1859_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
                    return v___x_1932_;
                }
            },
            6 => {
                return v___x_1935_;
            }
            7 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1949_;
            }
            9 => {
                if v_isShared_1955_ == 0 {
                    v___x_1957_ = v___x_1954_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
                    v___x_1957_ = v_reuseFailAlloc_1958_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed(
    mut v___x_1960_: *mut leanh::LeanObject,
    mut v_pre_1961_: *mut leanh::LeanObject,
    mut v_e_1962_: *mut leanh::LeanObject,
    mut v_post_1963_: *mut leanh::LeanObject,
    mut v___y_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(v___x_1960_, v_pre_1961_, v_e_1962_, v_post_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
    leanh::lean_dec(v___y_1968_);
    leanh::lean_dec_ref(v___y_1967_);
    leanh::lean_dec(v___y_1966_);
    leanh::lean_dec_ref(v___y_1965_);
    leanh::lean_dec(v___y_1964_);
    return v_res_1970_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(
    mut v_pre_1971_: *mut leanh::LeanObject,
    mut v_post_1972_: *mut leanh::LeanObject,
    mut v_e_1973_: *mut leanh::LeanObject,
    mut v_a_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_unused_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v_val_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2013_: u8 = 0;
    let mut v_a_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_1974_);
                v___x_1980_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_1980_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1980_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1980_, 2, v_a_1974_);
                v___x_1981_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(leanh::lean_box(0), v___x_1980_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
                if leanh::lean_obj_tag(v___x_1981_) == 0 {
                    v_a_1982_ = leanh::lean_ctor_get(v___x_1981_, 0);
                    v_isSharedCheck_2013_ = (!leanh::lean_is_exclusive(v___x_1981_)) as u8;
                    if v_isSharedCheck_2013_ == 0 {
                        v___x_1984_ = v___x_1981_;
                        v_isShared_1985_ = v_isSharedCheck_2013_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1982_);
                        leanh::lean_dec(v___x_1981_);
                        v___x_1984_ = leanh::lean_box(0);
                        v_isShared_1985_ = v_isSharedCheck_2013_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1973_);
                    leanh::lean_dec_ref(v_post_1972_);
                    leanh::lean_dec_ref(v_pre_1971_);
                    v_a_2014_ = leanh::lean_ctor_get(v___x_1981_, 0);
                    v_isSharedCheck_2021_ = (!leanh::lean_is_exclusive(v___x_1981_)) as u8;
                    if v_isSharedCheck_2021_ == 0 {
                        v___x_2016_ = v___x_1981_;
                        v_isShared_2017_ = v_isSharedCheck_2021_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2014_);
                        leanh::lean_dec(v___x_1981_);
                        v___x_2016_ = leanh::lean_box(0);
                        v_isShared_2017_ = v_isSharedCheck_2021_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_a_1982_, v_e_1973_);
                leanh::lean_dec(v_a_1982_);
                if leanh::lean_obj_tag(v___x_1986_) == 0 {
                    leanh::lean_del_object(v___x_1984_);
                    v___x_1987_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0;
                    leanh::lean_inc_ref(v_e_1973_);
                    v___f_1988_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 10, 4);
                    leanh::lean_closure_set(v___f_1988_, 0, v___x_1987_);
                    leanh::lean_closure_set(v___f_1988_, 1, v_pre_1971_);
                    leanh::lean_closure_set(v___f_1988_, 2, v_e_1973_);
                    leanh::lean_closure_set(v___f_1988_, 3, v_post_1972_);
                    v___x_1989_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v___f_1988_, v_a_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
                    if leanh::lean_obj_tag(v___x_1989_) == 0 {
                        v_a_1990_ = leanh::lean_ctor_get(v___x_1989_, 0);
                        leanh::lean_inc_n(v_a_1990_, 2);
                        leanh::lean_dec_ref_known(v___x_1989_, 1);
                        leanh::lean_inc(v_a_1974_);
                        v___f_1991_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_1991_, 0, v_a_1974_);
                        leanh::lean_closure_set(v___f_1991_, 1, v_e_1973_);
                        leanh::lean_closure_set(v___f_1991_, 2, v_a_1990_);
                        v___x_1992_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(leanh::lean_box(0), v___f_1991_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
                        if leanh::lean_obj_tag(v___x_1992_) == 0 {
                            v_isSharedCheck_1999_ =
                                (!leanh::lean_is_exclusive(v___x_1992_)) as u8;
                            if v_isSharedCheck_1999_ == 0 {
                                v_unused_2000_ = leanh::lean_ctor_get(v___x_1992_, 0);
                                leanh::lean_dec(v_unused_2000_);
                                v___x_1994_ = v___x_1992_;
                                v_isShared_1995_ = v_isSharedCheck_1999_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1992_);
                                v___x_1994_ = leanh::lean_box(0);
                                v_isShared_1995_ = v_isSharedCheck_1999_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1990_);
                            v_a_2001_ = leanh::lean_ctor_get(v___x_1992_, 0);
                            v_isSharedCheck_2008_ =
                                (!leanh::lean_is_exclusive(v___x_1992_)) as u8;
                            if v_isSharedCheck_2008_ == 0 {
                                v___x_2003_ = v___x_1992_;
                                v_isShared_2004_ = v_isSharedCheck_2008_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2001_);
                                leanh::lean_dec(v___x_1992_);
                                v___x_2003_ = leanh::lean_box(0);
                                v_isShared_2004_ = v_isSharedCheck_2008_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_1973_);
                        return v___x_1989_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1973_);
                    leanh::lean_dec_ref(v_post_1972_);
                    leanh::lean_dec_ref(v_pre_1971_);
                    v_val_2009_ = leanh::lean_ctor_get(v___x_1986_, 0);
                    leanh::lean_inc(v_val_2009_);
                    leanh::lean_dec_ref_known(v___x_1986_, 1);
                    if v_isShared_1985_ == 0 {
                        leanh::lean_ctor_set(v___x_1984_, 0, v_val_2009_);
                        v___x_2011_ = v___x_1984_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_val_2009_);
                        v___x_2011_ = v_reuseFailAlloc_2012_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1995_ == 0 {
                    leanh::lean_ctor_set(v___x_1994_, 0, v_a_1990_);
                    v___x_1997_ = v___x_1994_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1990_);
                    v___x_1997_ = v_reuseFailAlloc_1998_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1997_;
            }
            4 => {
                if v_isShared_2004_ == 0 {
                    v___x_2006_ = v___x_2003_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2007_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
                    v___x_2006_ = v_reuseFailAlloc_2007_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2006_;
            }
            6 => {
                return v___x_2011_;
            }
            7 => {
                if v_isShared_2017_ == 0 {
                    v___x_2019_ = v___x_2016_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2020_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
                    v___x_2019_ = v_reuseFailAlloc_2020_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(
    mut v_pre_2022_: *mut leanh::LeanObject,
    mut v_post_2023_: *mut leanh::LeanObject,
    mut v_e_2024_: *mut leanh::LeanObject,
    mut v_a_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v_e_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_2023_);
                leanh::lean_inc(v___y_2029_);
                leanh::lean_inc_ref(v___y_2028_);
                leanh::lean_inc(v___y_2027_);
                leanh::lean_inc_ref(v___y_2026_);
                leanh::lean_inc_ref(v_e_2024_);
                v___x_2031_ = leanh::lean_apply_6(
                    v_post_2023_,
                    v_e_2024_,
                    v___y_2026_,
                    v___y_2027_,
                    v___y_2028_,
                    v___y_2029_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2031_) == 0 {
                    v_a_2032_ = leanh::lean_ctor_get(v___x_2031_, 0);
                    v_isSharedCheck_2050_ = (!leanh::lean_is_exclusive(v___x_2031_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2034_ = v___x_2031_;
                        v_isShared_2035_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2032_);
                        leanh::lean_dec(v___x_2031_);
                        v___x_2034_ = leanh::lean_box(0);
                        v_isShared_2035_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2024_);
                    leanh::lean_dec_ref(v_post_2023_);
                    leanh::lean_dec_ref(v_pre_2022_);
                    v_a_2051_ = leanh::lean_ctor_get(v___x_2031_, 0);
                    v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v___x_2031_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2031_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2051_);
                        leanh::lean_dec(v___x_2031_);
                        v___x_2053_ = leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_2032_) {
                0 => {
                    leanh::lean_dec_ref(v_e_2024_);
                    leanh::lean_dec_ref(v_post_2023_);
                    leanh::lean_dec_ref(v_pre_2022_);
                    v_e_2036_ = leanh::lean_ctor_get(v_a_2032_, 0);
                    leanh::lean_inc_ref(v_e_2036_);
                    leanh::lean_dec_ref_known(v_a_2032_, 1);
                    if v_isShared_2035_ == 0 {
                        leanh::lean_ctor_set(v___x_2034_, 0, v_e_2036_);
                        v___x_2038_ = v___x_2034_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2039_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_e_2036_);
                        v___x_2038_ = v_reuseFailAlloc_2039_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_2034_);
                    leanh::lean_dec_ref(v_e_2024_);
                    v_e_2040_ = leanh::lean_ctor_get(v_a_2032_, 0);
                    leanh::lean_inc_ref(v_e_2040_);
                    leanh::lean_dec_ref_known(v_a_2032_, 1);
                    v___x_2041_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_2022_, v_post_2023_, v_e_2040_, v_a_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
                    return v___x_2041_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_2023_);
                    leanh::lean_dec_ref(v_pre_2022_);
                    v_e_x3f_2042_ = leanh::lean_ctor_get(v_a_2032_, 0);
                    leanh::lean_inc(v_e_x3f_2042_);
                    leanh::lean_dec_ref_known(v_a_2032_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_2042_) == 0 {
                        if v_isShared_2035_ == 0 {
                            leanh::lean_ctor_set(v___x_2034_, 0, v_e_2024_);
                            v___x_2044_ = v___x_2034_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2045_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_e_2024_);
                            v___x_2044_ = v_reuseFailAlloc_2045_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_2024_);
                        v_val_2046_ = leanh::lean_ctor_get(v_e_x3f_2042_, 0);
                        leanh::lean_inc(v_val_2046_);
                        leanh::lean_dec_ref_known(v_e_x3f_2042_, 1);
                        if v_isShared_2035_ == 0 {
                            leanh::lean_ctor_set(v___x_2034_, 0, v_val_2046_);
                            v___x_2048_ = v___x_2034_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2049_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_val_2046_);
                            v___x_2048_ = v_reuseFailAlloc_2049_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_2038_;
            }
            3 => {
                return v___x_2044_;
            }
            4 => {
                return v___x_2048_;
            }
            5 => {
                if v_isShared_2054_ == 0 {
                    v___x_2056_ = v___x_2053_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2___boxed(
    mut v_pre_2059_: *mut leanh::LeanObject,
    mut v_post_2060_: *mut leanh::LeanObject,
    mut v_e_2061_: *mut leanh::LeanObject,
    mut v_a_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
    mut v___y_2065_: *mut leanh::LeanObject,
    mut v___y_2066_: *mut leanh::LeanObject,
    mut v___y_2067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2068_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_2059_, v_post_2060_, v_e_2061_, v_a_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
    leanh::lean_dec(v___y_2066_);
    leanh::lean_dec_ref(v___y_2065_);
    leanh::lean_dec(v___y_2064_);
    leanh::lean_dec_ref(v___y_2063_);
    leanh::lean_dec(v_a_2062_);
    return v_res_2068_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1___boxed(
    mut v_pre_2069_: *mut leanh::LeanObject,
    mut v_post_2070_: *mut leanh::LeanObject,
    mut v_sz_2071_: *mut leanh::LeanObject,
    mut v_i_2072_: *mut leanh::LeanObject,
    mut v_bs_2073_: *mut leanh::LeanObject,
    mut v___y_2074_: *mut leanh::LeanObject,
    mut v___y_2075_: *mut leanh::LeanObject,
    mut v___y_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2080_: usize = 0;
    let mut v_i_boxed_2081_: usize = 0;
    let mut v_res_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2080_ = leanh::lean_unbox_usize(v_sz_2071_);
    leanh::lean_dec(v_sz_2071_);
    v_i_boxed_2081_ = leanh::lean_unbox_usize(v_i_2072_);
    leanh::lean_dec(v_i_2072_);
    v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_2069_, v_post_2070_, v_sz_boxed_2080_, v_i_boxed_2081_, v_bs_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    leanh::lean_dec(v___y_2076_);
    leanh::lean_dec_ref(v___y_2075_);
    leanh::lean_dec(v___y_2074_);
    return v_res_2082_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4___boxed(
    mut v_pre_2083_: *mut leanh::LeanObject,
    mut v_post_2084_: *mut leanh::LeanObject,
    mut v_x_2085_: *mut leanh::LeanObject,
    mut v_x_2086_: *mut leanh::LeanObject,
    mut v_x_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
    mut v___y_2090_: *mut leanh::LeanObject,
    mut v___y_2091_: *mut leanh::LeanObject,
    mut v___y_2092_: *mut leanh::LeanObject,
    mut v___y_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2094_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_2083_, v_post_2084_, v_x_2085_, v_x_2086_, v_x_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
    leanh::lean_dec(v___y_2092_);
    leanh::lean_dec_ref(v___y_2091_);
    leanh::lean_dec(v___y_2090_);
    leanh::lean_dec_ref(v___y_2089_);
    leanh::lean_dec(v___y_2088_);
    return v_res_2094_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___boxed(
    mut v_pre_2095_: *mut leanh::LeanObject,
    mut v_post_2096_: *mut leanh::LeanObject,
    mut v_e_2097_: *mut leanh::LeanObject,
    mut v_a_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
    mut v___y_2101_: *mut leanh::LeanObject,
    mut v___y_2102_: *mut leanh::LeanObject,
    mut v___y_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2104_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_2095_, v_post_2096_, v_e_2097_, v_a_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
    leanh::lean_dec(v___y_2102_);
    leanh::lean_dec_ref(v___y_2101_);
    leanh::lean_dec(v___y_2100_);
    leanh::lean_dec_ref(v___y_2099_);
    leanh::lean_dec(v_a_2098_);
    return v_res_2104_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = leanh::lean_box(0);
    v___x_2106_ = leanh::lean_unsigned_to_nat(16);
    v___x_2107_ = lean_mk_array(v___x_2106_, v___x_2105_);
    return v___x_2107_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0);
    v___x_2109_ = leanh::lean_unsigned_to_nat(0);
    v___x_2110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2110_, 0, v___x_2109_);
    leanh::lean_ctor_set(v___x_2110_, 1, v___x_2108_);
    return v___x_2110_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2111_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1);
    v___x_2112_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2112_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2112_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2112_, 2, v___x_2111_);
    return v___x_2112_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(
    mut v_input_2113_: *mut leanh::LeanObject,
    mut v_pre_2114_: *mut leanh::LeanObject,
    mut v_post_2115_: *mut leanh::LeanObject,
    mut v___y_2116_: *mut leanh::LeanObject,
    mut v___y_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v_unused_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2121_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2);
                v___x_2122_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(leanh::lean_box(0), v___x_2121_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
                v_a_2123_ = leanh::lean_ctor_get(v___x_2122_, 0);
                leanh::lean_inc(v_a_2123_);
                leanh::lean_dec_ref(v___x_2122_);
                v___x_2124_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_2114_, v_post_2115_, v_input_2113_, v_a_2123_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
                if leanh::lean_obj_tag(v___x_2124_) == 0 {
                    v_a_2125_ = leanh::lean_ctor_get(v___x_2124_, 0);
                    leanh::lean_inc(v_a_2125_);
                    leanh::lean_dec_ref_known(v___x_2124_, 1);
                    v___x_2126_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_2126_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_2126_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_2126_, 2, v_a_2123_);
                    v___x_2127_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(leanh::lean_box(0), v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
                    v_isSharedCheck_2134_ = (!leanh::lean_is_exclusive(v___x_2127_)) as u8;
                    if v_isSharedCheck_2134_ == 0 {
                        v_unused_2135_ = leanh::lean_ctor_get(v___x_2127_, 0);
                        leanh::lean_dec(v_unused_2135_);
                        v___x_2129_ = v___x_2127_;
                        v_isShared_2130_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2127_);
                        v___x_2129_ = leanh::lean_box(0);
                        v_isShared_2130_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2123_);
                    return v___x_2124_;
                }
            }
            1 => {
                if v_isShared_2130_ == 0 {
                    leanh::lean_ctor_set(v___x_2129_, 0, v_a_2125_);
                    v___x_2132_ = v___x_2129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2125_);
                    v___x_2132_ = v_reuseFailAlloc_2133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___boxed(
    mut v_input_2136_: *mut leanh::LeanObject,
    mut v_pre_2137_: *mut leanh::LeanObject,
    mut v_post_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
    mut v___y_2140_: *mut leanh::LeanObject,
    mut v___y_2141_: *mut leanh::LeanObject,
    mut v___y_2142_: *mut leanh::LeanObject,
    mut v___y_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(
        v_input_2136_,
        v_pre_2137_,
        v_post_2138_,
        v___y_2139_,
        v___y_2140_,
        v___y_2141_,
        v___y_2142_,
    );
    leanh::lean_dec(v___y_2142_);
    leanh::lean_dec_ref(v___y_2141_);
    leanh::lean_dec(v___y_2140_);
    leanh::lean_dec_ref(v___y_2139_);
    return v_res_2144_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(
    mut v_e_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
    mut v_a_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: u8 = 0;
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v_pre_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_a_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_a_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2194_: u8 = 0;
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v_a_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_unused_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2154_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0;
                v___x_2155_ = lean_find_expr(v___x_2154_, v_e_2148_);
                if leanh::lean_obj_tag(v___x_2155_) == 0 {
                    v___x_2156_ = 1;
                    v___x_2157_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_2157_, 0, v_e_2148_);
                    leanh::lean_ctor_set(v___x_2157_, 1, v___x_2155_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2157_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_2156_,
                    );
                    v___x_2158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2158_, 0, v___x_2157_);
                    return v___x_2158_;
                } else {
                    v_isSharedCheck_2207_ = (!leanh::lean_is_exclusive(v___x_2155_)) as u8;
                    if v_isSharedCheck_2207_ == 0 {
                        v_unused_2208_ = leanh::lean_ctor_get(v___x_2155_, 0);
                        leanh::lean_dec(v_unused_2208_);
                        v___x_2160_ = v___x_2155_;
                        v_isShared_2161_ = v_isSharedCheck_2207_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2155_);
                        v___x_2160_ = leanh::lean_box(0);
                        v_isShared_2161_ = v_isSharedCheck_2207_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pre_2162_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1;
                v___f_2163_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2;
                leanh::lean_inc_ref(v_e_2148_);
                v___x_2164_ =
                    l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(
                        v_e_2148_,
                        v_pre_2162_,
                        v___f_2163_,
                        v_a_2149_,
                        v_a_2150_,
                        v_a_2151_,
                        v_a_2152_,
                    );
                if leanh::lean_obj_tag(v___x_2164_) == 0 {
                    v_a_2165_ = leanh::lean_ctor_get(v___x_2164_, 0);
                    leanh::lean_inc_n(v_a_2165_, 2);
                    leanh::lean_dec_ref_known(v___x_2164_, 1);
                    v___x_2166_ =
                        l_Lean_Meta_mkEqRefl(v_a_2165_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
                    if leanh::lean_obj_tag(v___x_2166_) == 0 {
                        v_a_2167_ = leanh::lean_ctor_get(v___x_2166_, 0);
                        leanh::lean_inc(v_a_2167_);
                        leanh::lean_dec_ref_known(v___x_2166_, 1);
                        leanh::lean_inc(v_a_2165_);
                        v___x_2168_ = l_Lean_Meta_mkEq(
                            v_e_2148_, v_a_2165_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_,
                        );
                        if leanh::lean_obj_tag(v___x_2168_) == 0 {
                            v_a_2169_ = leanh::lean_ctor_get(v___x_2168_, 0);
                            v_isSharedCheck_2182_ =
                                (!leanh::lean_is_exclusive(v___x_2168_)) as u8;
                            if v_isSharedCheck_2182_ == 0 {
                                v___x_2171_ = v___x_2168_;
                                v_isShared_2172_ = v_isSharedCheck_2182_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2169_);
                                leanh::lean_dec(v___x_2168_);
                                v___x_2171_ = leanh::lean_box(0);
                                v_isShared_2172_ = v_isSharedCheck_2182_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2167_);
                            leanh::lean_dec(v_a_2165_);
                            leanh::lean_del_object(v___x_2160_);
                            v_a_2183_ = leanh::lean_ctor_get(v___x_2168_, 0);
                            v_isSharedCheck_2190_ =
                                (!leanh::lean_is_exclusive(v___x_2168_)) as u8;
                            if v_isSharedCheck_2190_ == 0 {
                                v___x_2185_ = v___x_2168_;
                                v_isShared_2186_ = v_isSharedCheck_2190_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2183_);
                                leanh::lean_dec(v___x_2168_);
                                v___x_2185_ = leanh::lean_box(0);
                                v_isShared_2186_ = v_isSharedCheck_2190_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2165_);
                        leanh::lean_del_object(v___x_2160_);
                        leanh::lean_dec_ref(v_e_2148_);
                        v_a_2191_ = leanh::lean_ctor_get(v___x_2166_, 0);
                        v_isSharedCheck_2198_ =
                            (!leanh::lean_is_exclusive(v___x_2166_)) as u8;
                        if v_isSharedCheck_2198_ == 0 {
                            v___x_2193_ = v___x_2166_;
                            v_isShared_2194_ = v_isSharedCheck_2198_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2191_);
                            leanh::lean_dec(v___x_2166_);
                            v___x_2193_ = leanh::lean_box(0);
                            v_isShared_2194_ = v_isSharedCheck_2198_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2160_);
                    leanh::lean_dec_ref(v_e_2148_);
                    v_a_2199_ = leanh::lean_ctor_get(v___x_2164_, 0);
                    v_isSharedCheck_2206_ = (!leanh::lean_is_exclusive(v___x_2164_)) as u8;
                    if v_isSharedCheck_2206_ == 0 {
                        v___x_2201_ = v___x_2164_;
                        v_isShared_2202_ = v_isSharedCheck_2206_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2199_);
                        leanh::lean_dec(v___x_2164_);
                        v___x_2201_ = leanh::lean_box(0);
                        v_isShared_2202_ = v_isSharedCheck_2206_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2173_ = 1;
                v___x_2174_ = l_Lean_Meta_mkExpectedPropHint(v_a_2167_, v_a_2169_);
                if v_isShared_2161_ == 0 {
                    leanh::lean_ctor_set(v___x_2160_, 0, v___x_2174_);
                    v___x_2176_ = v___x_2160_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2174_);
                    v___x_2176_ = v_reuseFailAlloc_2181_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2177_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_2177_, 0, v_a_2165_);
                leanh::lean_ctor_set(v___x_2177_, 1, v___x_2176_);
                leanh::lean_ctor_set_uint8(
                    v___x_2177_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_2173_,
                );
                if v_isShared_2172_ == 0 {
                    leanh::lean_ctor_set(v___x_2171_, 0, v___x_2177_);
                    v___x_2179_ = v___x_2171_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
                    v___x_2179_ = v_reuseFailAlloc_2180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2179_;
            }
            5 => {
                if v_isShared_2186_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
                    v___x_2188_ = v_reuseFailAlloc_2189_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2188_;
            }
            7 => {
                if v_isShared_2194_ == 0 {
                    v___x_2196_ = v___x_2193_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2197_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
                    v___x_2196_ = v_reuseFailAlloc_2197_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2196_;
            }
            9 => {
                if v_isShared_2202_ == 0 {
                    v___x_2204_ = v___x_2201_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2205_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
                    v___x_2204_ = v_reuseFailAlloc_2205_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___boxed(
    mut v_e_2209_: *mut leanh::LeanObject,
    mut v_a_2210_: *mut leanh::LeanObject,
    mut v_a_2211_: *mut leanh::LeanObject,
    mut v_a_2212_: *mut leanh::LeanObject,
    mut v_a_2213_: *mut leanh::LeanObject,
    mut v_a_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(
        v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_,
    );
    leanh::lean_dec(v_a_2213_);
    leanh::lean_dec_ref(v_a_2212_);
    leanh::lean_dec(v_a_2211_);
    leanh::lean_dec_ref(v_a_2210_);
    return v_res_2215_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(
    mut v_00_u03b2_2216_: *mut leanh::LeanObject,
    mut v_m_2217_: *mut leanh::LeanObject,
    mut v_a_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_2217_, v_a_2218_);
    return v___x_2219_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_2220_: *mut leanh::LeanObject,
    mut v_m_2221_: *mut leanh::LeanObject,
    mut v_a_2222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(v_00_u03b2_2220_, v_m_2221_, v_a_2222_);
    leanh::lean_dec_ref(v_a_2222_);
    leanh::lean_dec_ref(v_m_2221_);
    return v_res_2223_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_2224_: *mut leanh::LeanObject,
    mut v_ref_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2229_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2225_);
    return v___x_2229_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_2230_: *mut leanh::LeanObject,
    mut v_ref_2231_: *mut leanh::LeanObject,
    mut v___y_2232_: *mut leanh::LeanObject,
    mut v___y_2233_: *mut leanh::LeanObject,
    mut v___y_2234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2235_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2230_, v_ref_2231_, v___y_2232_, v___y_2233_);
    leanh::lean_dec(v___y_2233_);
    leanh::lean_dec_ref(v___y_2232_);
    return v_res_2235_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(
    mut v_00_u03b1_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
    mut v___y_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
    return v___x_2240_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___boxed(
    mut v_00_u03b1_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: *mut leanh::LeanObject,
    mut v___y_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2245_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_2241_, v___y_2242_, v___y_2243_);
    leanh::lean_dec(v___y_2243_);
    leanh::lean_dec_ref(v___y_2242_);
    return v_res_2245_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(
    mut v_00_u03b1_2246_: *mut leanh::LeanObject,
    mut v_x_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
    return v___x_2254_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b1_2255_: *mut leanh::LeanObject,
    mut v_x_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
    mut v___y_2258_: *mut leanh::LeanObject,
    mut v___y_2259_: *mut leanh::LeanObject,
    mut v___y_2260_: *mut leanh::LeanObject,
    mut v___y_2261_: *mut leanh::LeanObject,
    mut v___y_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2263_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(v_00_u03b1_2255_, v_x_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
    leanh::lean_dec(v___y_2261_);
    leanh::lean_dec_ref(v___y_2260_);
    leanh::lean_dec(v___y_2259_);
    leanh::lean_dec_ref(v___y_2258_);
    leanh::lean_dec(v___y_2257_);
    return v_res_2263_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6(
    mut v_00_u03b2_2264_: *mut leanh::LeanObject,
    mut v_m_2265_: *mut leanh::LeanObject,
    mut v_a_2266_: *mut leanh::LeanObject,
    mut v_b_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v_m_2265_, v_a_2266_, v_b_2267_);
    return v___x_2268_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b2_2269_: *mut leanh::LeanObject,
    mut v_a_2270_: *mut leanh::LeanObject,
    mut v_x_2271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2272_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2270_, v_x_2271_);
    return v___x_2272_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b2_2273_: *mut leanh::LeanObject,
    mut v_a_2274_: *mut leanh::LeanObject,
    mut v_x_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2273_, v_a_2274_, v_x_2275_);
    leanh::lean_dec(v_x_2275_);
    leanh::lean_dec_ref(v_a_2274_);
    return v_res_2276_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(
    mut v_00_u03b2_2277_: *mut leanh::LeanObject,
    mut v_a_2278_: *mut leanh::LeanObject,
    mut v_x_2279_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2280_: u8 = 0;
    v___x_2280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2278_, v_x_2279_);
    return v___x_2280_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___boxed(
    mut v_00_u03b2_2281_: *mut leanh::LeanObject,
    mut v_a_2282_: *mut leanh::LeanObject,
    mut v_x_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2284_: u8 = 0;
    let mut v_r_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_2281_, v_a_2282_, v_x_2283_);
    leanh::lean_dec(v_x_2283_);
    leanh::lean_dec_ref(v_a_2282_);
    v_r_2285_ = leanh::lean_box((v_res_2284_) as usize);
    return v_r_2285_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11(
    mut v_00_u03b2_2286_: *mut leanh::LeanObject,
    mut v_data_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_data_2287_);
    return v___x_2288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b2_2289_: *mut leanh::LeanObject,
    mut v_a_2290_: *mut leanh::LeanObject,
    mut v_b_2291_: *mut leanh::LeanObject,
    mut v_x_2292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2290_, v_b_2291_, v_x_2292_);
    return v___x_2293_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12(
    mut v_00_u03b2_2294_: *mut leanh::LeanObject,
    mut v_i_2295_: *mut leanh::LeanObject,
    mut v_source_2296_: *mut leanh::LeanObject,
    mut v_target_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_2295_, v_source_2296_, v_target_2297_);
    return v___x_2298_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(
    mut v_00_u03b2_2299_: *mut leanh::LeanObject,
    mut v_x_2300_: *mut leanh::LeanObject,
    mut v_x_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_2300_, v_x_2301_);
    return v___x_2302_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
}