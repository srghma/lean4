// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
// Imports: Init.Simproc Lean.Meta.Tactic.Simp.Simproc Lean.Meta.CtorRecognizer
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_simp, lean_uint64_lor,
    lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_headBeta, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_isFalse, l_Lean_Expr_isTrue, l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkEqFalse_x27, l_Lean_Meta_mkNoConfusion};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::{
    initialize_Lean_Meta_CtorRecognizer, l_Lean_Meta_constructorApp_x27_x3f,
    runtime_initialize_Lean_Meta_CtorRecognizer,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_addSEvalprocBuiltinAttr,
    l_Lean_Meta_Simp_addSimprocBuiltinAttr, l_Lean_Meta_Simp_registerBuiltinDSimproc,
    l_Lean_Meta_Simp_registerBuiltinSimproc, runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Result_getProof;
pub static l_reduceIte___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
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
static mut l_reduceIte___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__0_value) as *mut leanh::LeanObject;
pub static l_reduceIte___closed__1_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 116, 101, 0],
    };
static mut l_reduceIte___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__1_value) as *mut leanh::LeanObject;
pub static l_reduceIte___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceIte___closed__1_value) as *mut leanh::LeanObject,
            18356704233129443855 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceIte___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__2_value) as *mut leanh::LeanObject;
pub static l_reduceIte___closed__3_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
        ],
    };
static mut l_reduceIte___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__3_value) as *mut leanh::LeanObject;
pub static l_reduceIte___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceIte___closed__3_value) as *mut leanh::LeanObject,
            15684782314253460228 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceIte___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__4_value) as *mut leanh::LeanObject;
pub static l_reduceIte___closed__5_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 116, 114, 117, 101, 0,
        ],
    };
static mut l_reduceIte___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__5_value) as *mut leanh::LeanObject;
pub static l_reduceIte___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceIte___closed__5_value) as *mut leanh::LeanObject,
            7490975742882862809 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceIte___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut leanh::LeanObject,13377587881735534081 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceIte___closed__2_value) as *mut leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: leanh::LeanArrayObject<6> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_reduceDIte___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [100, 105, 116, 101, 0],
    };
static mut l_reduceDIte___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__0_value) as *mut leanh::LeanObject;
pub static l_reduceDIte___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceDIte___closed__0_value) as *mut leanh::LeanObject,
            8391571994004792969 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceDIte___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__1_value) as *mut leanh::LeanObject;
pub static l_reduceDIte___closed__2_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [111, 102, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_reduceDIte___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__2_value) as *mut leanh::LeanObject;
pub static l_reduceDIte___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceDIte___closed__2_value) as *mut leanh::LeanObject,
            712644580193758902 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceDIte___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__3_value) as *mut leanh::LeanObject;
static mut l_reduceDIte___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceDIte___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_reduceDIte___closed__5_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
        ],
    };
static mut l_reduceDIte___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__5_value) as *mut leanh::LeanObject;
pub static l_reduceDIte___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceDIte___closed__5_value) as *mut leanh::LeanObject,
            15303888708270464921 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceDIte___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__6_value) as *mut leanh::LeanObject;
pub static l_reduceDIte___closed__7_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [111, 102, 95, 101, 113, 95, 116, 114, 117, 101, 0],
    };
static mut l_reduceDIte___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__7_value) as *mut leanh::LeanObject;
pub static l_reduceDIte___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceDIte___closed__7_value) as *mut leanh::LeanObject,
            12884550255617431732 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceDIte___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__8_value) as *mut leanh::LeanObject;
static mut l_reduceDIte___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceDIte___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_reduceDIte___closed__10_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 116, 114, 117, 101, 0,
        ],
    };
static mut l_reduceDIte___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__10_value) as *mut leanh::LeanObject;
pub static l_reduceDIte___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceDIte___closed__10_value) as *mut leanh::LeanObject,
            187051596005140493 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceDIte___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 100, 117, 99, 101, 68, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut leanh::LeanObject,5427593982451803422 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceDIte___closed__1_value) as *mut leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: leanh::LeanArrayObject<6> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_dreduceIte___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
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
static mut l_dreduceIte___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__0_value) as *mut leanh::LeanObject;
pub static l_dreduceIte___closed__1_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0],
    };
static mut l_dreduceIte___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__1_value) as *mut leanh::LeanObject;
pub static l_dreduceIte___closed__2_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [105, 115, 70, 97, 108, 115, 101, 0],
    };
static mut l_dreduceIte___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__2_value) as *mut leanh::LeanObject;
static l_dreduceIte___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_dreduceIte___closed__1_value) as *mut leanh::LeanObject,
            4342836574150310743 as *mut leanh::LeanObject,
        ],
    };
pub static l_dreduceIte___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_dreduceIte___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_dreduceIte___closed__2_value) as *mut leanh::LeanObject,
            14734865452941588245 as *mut leanh::LeanObject,
        ],
    };
static mut l_dreduceIte___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__3_value) as *mut leanh::LeanObject;
pub static l_dreduceIte___closed__4_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 115, 84, 114, 117, 101, 0],
    };
static mut l_dreduceIte___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__4_value) as *mut leanh::LeanObject;
static l_dreduceIte___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_dreduceIte___closed__1_value) as *mut leanh::LeanObject,
            4342836574150310743 as *mut leanh::LeanObject,
        ],
    };
pub static l_dreduceIte___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_dreduceIte___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_dreduceIte___closed__4_value) as *mut leanh::LeanObject,
            83052734847462153 as *mut leanh::LeanObject,
        ],
    };
static mut l_dreduceIte___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 114, 101, 100, 117, 99, 101, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value) as *mut leanh::LeanObject,18396871770522245140 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 114, 101, 100, 117, 99, 101, 68, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value) as *mut leanh::LeanObject,3968518033955806430 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_reduceCtorEq___lam__2___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 97, 108, 115, 101, 0],
    };
static mut l_reduceCtorEq___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_reduceCtorEq___lam__2___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceCtorEq___lam__2___closed__0_value)
                as *mut leanh::LeanObject,
            907667957179513571 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceCtorEq___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___lam__2___closed__1_value) as *mut leanh::LeanObject;
static mut l_reduceCtorEq___lam__2___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_reduceCtorEq___lam__2___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_reduceCtorEq___lam__2___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_reduceCtorEq___lam__2___closed__3: u64 = 0;
static mut l_reduceCtorEq___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_reduceCtorEq___closed__0: u64 = 0;
pub static l_reduceCtorEq___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_reduceCtorEq___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__1_value) as *mut leanh::LeanObject;
pub static l_reduceCtorEq___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceCtorEq___closed__1_value) as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceCtorEq___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__2_value) as *mut leanh::LeanObject;
pub static l_reduceCtorEq___closed__3_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [104, 0],
    };
static mut l_reduceCtorEq___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__3_value) as *mut leanh::LeanObject;
pub static l_reduceCtorEq___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_reduceCtorEq___closed__3_value) as *mut leanh::LeanObject,
            8738205681931236784 as *mut leanh::LeanObject,
        ],
    };
static mut l_reduceCtorEq___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__4_value) as *mut leanh::LeanObject;
pub static l_reduceCtorEq___boxed__const__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [3 as *mut leanh::LeanObject],
    };
pub static mut l_reduceCtorEq___boxed__const__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___boxed__const__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut leanh::LeanObject,233589347272681201 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceCtorEq___closed__2_value) as *mut leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: leanh::LeanArrayObject<4> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_reduceIte(
    mut v_e_1207_: *mut leanh::LeanObject,
    mut v_a_1208_: *mut leanh::LeanObject,
    mut v_a_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
    mut v_a_1211_: *mut leanh::LeanObject,
    mut v_a_1212_: *mut leanh::LeanObject,
    mut v_a_1213_: *mut leanh::LeanObject,
    mut v_a_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v_arg_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    let mut v_arg_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: u8 = 0;
    let mut v_arg_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v_arg_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v_arg_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: u8 = 0;
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v_expr_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: u8 = 0;
    let mut v___x_1251_: u8 = 0;
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_a_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1280_: u8 = 0;
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut v_a_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1305_: u8 = 0;
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_a_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1314_: u8 = 0;
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut v_a_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1216_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1207_, v_a_1212_);
                if leanh::lean_obj_tag(v___x_1216_) == 0 {
                    v_a_1217_ = leanh::lean_ctor_get(v___x_1216_, 0);
                    v_isSharedCheck_1315_ = (!leanh::lean_is_exclusive(v___x_1216_)) as u8;
                    if v_isSharedCheck_1315_ == 0 {
                        v___x_1219_ = v___x_1216_;
                        v_isShared_1220_ = v_isSharedCheck_1315_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1217_);
                        leanh::lean_dec(v___x_1216_);
                        v___x_1219_ = leanh::lean_box(0);
                        v_isShared_1220_ = v_isSharedCheck_1315_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1316_ = leanh::lean_ctor_get(v___x_1216_, 0);
                    v_isSharedCheck_1323_ = (!leanh::lean_is_exclusive(v___x_1216_)) as u8;
                    if v_isSharedCheck_1323_ == 0 {
                        v___x_1318_ = v___x_1216_;
                        v_isShared_1319_ = v_isSharedCheck_1323_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1316_);
                        leanh::lean_dec(v___x_1216_);
                        v___x_1318_ = leanh::lean_box(0);
                        v_isShared_1319_ = v_isSharedCheck_1323_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1226_ = l_Lean_Expr_cleanupAnnotations(v_a_1217_);
                v___x_1227_ = l_Lean_Expr_isApp(v___x_1226_);
                if v___x_1227_ == 0 {
                    leanh::lean_dec_ref(v___x_1226_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1228_ = leanh::lean_ctor_get(v___x_1226_, 1);
                    leanh::lean_inc_ref(v_arg_1228_);
                    v___x_1229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1226_);
                    v___x_1230_ = l_Lean_Expr_isApp(v___x_1229_);
                    if v___x_1230_ == 0 {
                        leanh::lean_dec_ref(v___x_1229_);
                        leanh::lean_dec_ref(v_arg_1228_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_1231_ = leanh::lean_ctor_get(v___x_1229_, 1);
                        leanh::lean_inc_ref(v_arg_1231_);
                        v___x_1232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1229_);
                        v___x_1233_ = l_Lean_Expr_isApp(v___x_1232_);
                        if v___x_1233_ == 0 {
                            leanh::lean_dec_ref(v___x_1232_);
                            leanh::lean_dec_ref(v_arg_1231_);
                            leanh::lean_dec_ref(v_arg_1228_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_1234_ = leanh::lean_ctor_get(v___x_1232_, 1);
                            leanh::lean_inc_ref(v_arg_1234_);
                            v___x_1235_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1232_);
                            v___x_1236_ = l_Lean_Expr_isApp(v___x_1235_);
                            if v___x_1236_ == 0 {
                                leanh::lean_dec_ref(v___x_1235_);
                                leanh::lean_dec_ref(v_arg_1234_);
                                leanh::lean_dec_ref(v_arg_1231_);
                                leanh::lean_dec_ref(v_arg_1228_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_1237_ = leanh::lean_ctor_get(v___x_1235_, 1);
                                leanh::lean_inc_ref(v_arg_1237_);
                                v___x_1238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1235_);
                                v___x_1239_ = l_Lean_Expr_isApp(v___x_1238_);
                                if v___x_1239_ == 0 {
                                    leanh::lean_dec_ref(v___x_1238_);
                                    leanh::lean_dec_ref(v_arg_1237_);
                                    leanh::lean_dec_ref(v_arg_1234_);
                                    leanh::lean_dec_ref(v_arg_1231_);
                                    leanh::lean_dec_ref(v_arg_1228_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_1240_ = leanh::lean_ctor_get(v___x_1238_, 1);
                                    leanh::lean_inc_ref(v_arg_1240_);
                                    v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1238_);
                                    v___x_1242_ = l_reduceIte___closed__2;
                                    v___x_1243_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1242_);
                                    if v___x_1243_ == 0 {
                                        leanh::lean_dec_ref(v___x_1241_);
                                        leanh::lean_dec_ref(v_arg_1240_);
                                        leanh::lean_dec_ref(v_arg_1237_);
                                        leanh::lean_dec_ref(v_arg_1234_);
                                        leanh::lean_dec_ref(v_arg_1231_);
                                        leanh::lean_dec_ref(v_arg_1228_);
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_del_object(v___x_1219_);
                                        leanh::lean_inc(v_a_1214_);
                                        leanh::lean_inc_ref(v_a_1213_);
                                        leanh::lean_inc(v_a_1212_);
                                        leanh::lean_inc_ref(v_a_1211_);
                                        leanh::lean_inc(v_a_1210_);
                                        leanh::lean_inc_ref(v_a_1209_);
                                        leanh::lean_inc(v_a_1208_);
                                        leanh::lean_inc_ref(v_arg_1237_);
                                        v___x_1244_ = lean_simp(
                                            v_arg_1237_,
                                            v_a_1208_,
                                            v_a_1209_,
                                            v_a_1210_,
                                            v_a_1211_,
                                            v_a_1212_,
                                            v_a_1213_,
                                            v_a_1214_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1244_) == 0 {
                                            v_a_1245_ = leanh::lean_ctor_get(v___x_1244_, 0);
                                            v_isSharedCheck_1306_ =
                                                (!leanh::lean_is_exclusive(v___x_1244_))
                                                    as u8;
                                            if v_isSharedCheck_1306_ == 0 {
                                                v___x_1247_ = v___x_1244_;
                                                v_isShared_1248_ = v_isSharedCheck_1306_;
                                                state = 4;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1245_);
                                                leanh::lean_dec(v___x_1244_);
                                                v___x_1247_ = leanh::lean_box(0);
                                                v_isShared_1248_ = v_isSharedCheck_1306_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_1241_);
                                            leanh::lean_dec_ref(v_arg_1240_);
                                            leanh::lean_dec_ref(v_arg_1237_);
                                            leanh::lean_dec_ref(v_arg_1234_);
                                            leanh::lean_dec_ref(v_arg_1231_);
                                            leanh::lean_dec_ref(v_arg_1228_);
                                            v_a_1307_ = leanh::lean_ctor_get(v___x_1244_, 0);
                                            v_isSharedCheck_1314_ =
                                                (!leanh::lean_is_exclusive(v___x_1244_))
                                                    as u8;
                                            if v_isSharedCheck_1314_ == 0 {
                                                v___x_1309_ = v___x_1244_;
                                                v_isShared_1310_ = v_isSharedCheck_1314_;
                                                state = 14;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1307_);
                                                leanh::lean_dec(v___x_1244_);
                                                v___x_1309_ = leanh::lean_box(0);
                                                v_isShared_1310_ = v_isSharedCheck_1314_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1222_ = l_reduceIte___closed__0;
                if v_isShared_1220_ == 0 {
                    leanh::lean_ctor_set(v___x_1219_, 0, v___x_1222_);
                    v___x_1224_ = v___x_1219_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1224_;
            }
            4 => {
                v_expr_1249_ = leanh::lean_ctor_get(v_a_1245_, 0);
                leanh::lean_inc_ref(v_expr_1249_);
                v___x_1250_ = l_Lean_Expr_isTrue(v_expr_1249_);
                if v___x_1250_ == 0 {
                    leanh::lean_inc_ref(v_expr_1249_);
                    v___x_1251_ = l_Lean_Expr_isFalse(v_expr_1249_);
                    if v___x_1251_ == 0 {
                        leanh::lean_dec(v_a_1245_);
                        leanh::lean_dec_ref(v___x_1241_);
                        leanh::lean_dec_ref(v_arg_1240_);
                        leanh::lean_dec_ref(v_arg_1237_);
                        leanh::lean_dec_ref(v_arg_1234_);
                        leanh::lean_dec_ref(v_arg_1231_);
                        leanh::lean_dec_ref(v_arg_1228_);
                        v___x_1252_ = l_reduceIte___closed__0;
                        if v_isShared_1248_ == 0 {
                            leanh::lean_ctor_set(v___x_1247_, 0, v___x_1252_);
                            v___x_1254_ = v___x_1247_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1255_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
                            v___x_1254_ = v_reuseFailAlloc_1255_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1247_);
                        v___x_1256_ = l_Lean_Meta_Simp_Result_getProof(
                            v_a_1245_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_,
                        );
                        if leanh::lean_obj_tag(v___x_1256_) == 0 {
                            v_a_1257_ = leanh::lean_ctor_get(v___x_1256_, 0);
                            v_isSharedCheck_1272_ =
                                (!leanh::lean_is_exclusive(v___x_1256_)) as u8;
                            if v_isSharedCheck_1272_ == 0 {
                                v___x_1259_ = v___x_1256_;
                                v_isShared_1260_ = v_isSharedCheck_1272_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1257_);
                                leanh::lean_dec(v___x_1256_);
                                v___x_1259_ = leanh::lean_box(0);
                                v_isShared_1260_ = v_isSharedCheck_1272_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1241_);
                            leanh::lean_dec_ref(v_arg_1240_);
                            leanh::lean_dec_ref(v_arg_1237_);
                            leanh::lean_dec_ref(v_arg_1234_);
                            leanh::lean_dec_ref(v_arg_1231_);
                            leanh::lean_dec_ref(v_arg_1228_);
                            v_a_1273_ = leanh::lean_ctor_get(v___x_1256_, 0);
                            v_isSharedCheck_1280_ =
                                (!leanh::lean_is_exclusive(v___x_1256_)) as u8;
                            if v_isSharedCheck_1280_ == 0 {
                                v___x_1275_ = v___x_1256_;
                                v_isShared_1276_ = v_isSharedCheck_1280_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1273_);
                                leanh::lean_dec(v___x_1256_);
                                v___x_1275_ = leanh::lean_box(0);
                                v_isShared_1276_ = v_isSharedCheck_1280_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1247_);
                    v___x_1281_ = l_Lean_Meta_Simp_Result_getProof(
                        v_a_1245_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_,
                    );
                    if leanh::lean_obj_tag(v___x_1281_) == 0 {
                        v_a_1282_ = leanh::lean_ctor_get(v___x_1281_, 0);
                        v_isSharedCheck_1297_ =
                            (!leanh::lean_is_exclusive(v___x_1281_)) as u8;
                        if v_isSharedCheck_1297_ == 0 {
                            v___x_1284_ = v___x_1281_;
                            v_isShared_1285_ = v_isSharedCheck_1297_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1282_);
                            leanh::lean_dec(v___x_1281_);
                            v___x_1284_ = leanh::lean_box(0);
                            v_isShared_1285_ = v_isSharedCheck_1297_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1241_);
                        leanh::lean_dec_ref(v_arg_1240_);
                        leanh::lean_dec_ref(v_arg_1237_);
                        leanh::lean_dec_ref(v_arg_1234_);
                        leanh::lean_dec_ref(v_arg_1231_);
                        leanh::lean_dec_ref(v_arg_1228_);
                        v_a_1298_ = leanh::lean_ctor_get(v___x_1281_, 0);
                        v_isSharedCheck_1305_ =
                            (!leanh::lean_is_exclusive(v___x_1281_)) as u8;
                        if v_isSharedCheck_1305_ == 0 {
                            v___x_1300_ = v___x_1281_;
                            v_isShared_1301_ = v_isSharedCheck_1305_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1298_);
                            leanh::lean_dec(v___x_1281_);
                            v___x_1300_ = leanh::lean_box(0);
                            v_isShared_1301_ = v_isSharedCheck_1305_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_1254_;
            }
            6 => {
                v___x_1261_ = l_reduceIte___closed__4;
                v___x_1262_ = l_Lean_Expr_constLevels_x21(v___x_1241_);
                leanh::lean_dec_ref(v___x_1241_);
                v___x_1263_ = l_Lean_mkConst(v___x_1261_, v___x_1262_);
                leanh::lean_inc_ref(v_arg_1228_);
                v___x_1264_ = l_Lean_mkApp5(
                    v___x_1263_,
                    v_arg_1240_,
                    v_arg_1237_,
                    v_arg_1234_,
                    v_arg_1231_,
                    v_arg_1228_,
                );
                v___x_1265_ = l_Lean_Expr_app___override(v___x_1264_, v_a_1257_);
                v___x_1266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1266_, 0, v___x_1265_);
                v___x_1267_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1267_, 0, v_arg_1228_);
                leanh::lean_ctor_set(v___x_1267_, 1, v___x_1266_);
                leanh::lean_ctor_set_uint8(
                    v___x_1267_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1243_,
                );
                v___x_1268_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
                if v_isShared_1260_ == 0 {
                    leanh::lean_ctor_set(v___x_1259_, 0, v___x_1268_);
                    v___x_1270_ = v___x_1259_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1271_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
                    v___x_1270_ = v_reuseFailAlloc_1271_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1270_;
            }
            8 => {
                if v_isShared_1276_ == 0 {
                    v___x_1278_ = v___x_1275_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1279_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
                    v___x_1278_ = v_reuseFailAlloc_1279_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1278_;
            }
            10 => {
                v___x_1286_ = l_reduceIte___closed__6;
                v___x_1287_ = l_Lean_Expr_constLevels_x21(v___x_1241_);
                leanh::lean_dec_ref(v___x_1241_);
                v___x_1288_ = l_Lean_mkConst(v___x_1286_, v___x_1287_);
                leanh::lean_inc_ref(v_arg_1231_);
                v___x_1289_ = l_Lean_mkApp5(
                    v___x_1288_,
                    v_arg_1240_,
                    v_arg_1237_,
                    v_arg_1234_,
                    v_arg_1231_,
                    v_arg_1228_,
                );
                v___x_1290_ = l_Lean_Expr_app___override(v___x_1289_, v_a_1282_);
                v___x_1291_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1291_, 0, v___x_1290_);
                v___x_1292_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1292_, 0, v_arg_1231_);
                leanh::lean_ctor_set(v___x_1292_, 1, v___x_1291_);
                leanh::lean_ctor_set_uint8(
                    v___x_1292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1243_,
                );
                v___x_1293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1293_, 0, v___x_1292_);
                if v_isShared_1285_ == 0 {
                    leanh::lean_ctor_set(v___x_1284_, 0, v___x_1293_);
                    v___x_1295_ = v___x_1284_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
                    v___x_1295_ = v_reuseFailAlloc_1296_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1295_;
            }
            12 => {
                if v_isShared_1301_ == 0 {
                    v___x_1303_ = v___x_1300_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
                    v___x_1303_ = v_reuseFailAlloc_1304_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1303_;
            }
            14 => {
                if v_isShared_1310_ == 0 {
                    v___x_1312_ = v___x_1309_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
                    v___x_1312_ = v_reuseFailAlloc_1313_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1312_;
            }
            16 => {
                if v_isShared_1319_ == 0 {
                    v___x_1321_ = v___x_1318_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
                    v___x_1321_ = v_reuseFailAlloc_1322_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_reduceIte___boxed(
    mut v_e_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
    mut v_a_1327_: *mut leanh::LeanObject,
    mut v_a_1328_: *mut leanh::LeanObject,
    mut v_a_1329_: *mut leanh::LeanObject,
    mut v_a_1330_: *mut leanh::LeanObject,
    mut v_a_1331_: *mut leanh::LeanObject,
    mut v_a_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1333_ = l_reduceIte(
        v_e_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_,
    );
    leanh::lean_dec(v_a_1331_);
    leanh::lean_dec_ref(v_a_1330_);
    leanh::lean_dec(v_a_1329_);
    leanh::lean_dec_ref(v_a_1328_);
    leanh::lean_dec(v_a_1327_);
    leanh::lean_dec_ref(v_a_1326_);
    leanh::lean_dec(v_a_1325_);
    return v_res_1333_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1352_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1353_ =
        leanh::lean_alloc_closure(l_reduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1354_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1351_, v___x_1352_, v___x_1353_);
    return v___x_1354_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15____boxed(
    mut v_a_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
    return v_res_1356_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ =
        leanh::lean_alloc_closure(l_reduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1358_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1358_, 0, v___x_1357_);
    return v___x_1358_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1361_ = 0;
    v___x_1362_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
    v___x_1363_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1360_, v___x_1361_, v___x_1362_);
    return v___x_1363_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(
    mut v_a_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1365_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
    return v_res_1365_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_()
-> *mut leanh::LeanObject {
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1368_ = 0;
    v___x_1369_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
    v___x_1370_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1367_, v___x_1368_, v___x_1369_);
    return v___x_1370_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19____boxed(
    mut v_a_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
    return v_res_1372_;
}
pub unsafe fn _init_l_reduceDIte___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = leanh::lean_box(0);
    v___x_1380_ = l_reduceDIte___closed__3;
    v___x_1381_ = l_Lean_mkConst(v___x_1380_, v___x_1379_);
    return v___x_1381_;
}
pub unsafe fn _init_l_reduceDIte___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = leanh::lean_box(0);
    v___x_1389_ = l_reduceDIte___closed__8;
    v___x_1390_ = l_Lean_mkConst(v___x_1389_, v___x_1388_);
    return v___x_1390_;
}
pub unsafe fn l_reduceDIte(
    mut v_e_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v_arg_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v_arg_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v_arg_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: u8 = 0;
    let mut v_arg_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut v_arg_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v_expr_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v_a_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1476_: u8 = 0;
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_a_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_a_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut v_a_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1403_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1394_, v_a_1399_);
                if leanh::lean_obj_tag(v___x_1403_) == 0 {
                    v_a_1404_ = leanh::lean_ctor_get(v___x_1403_, 0);
                    v_isSharedCheck_1510_ = (!leanh::lean_is_exclusive(v___x_1403_)) as u8;
                    if v_isSharedCheck_1510_ == 0 {
                        v___x_1406_ = v___x_1403_;
                        v_isShared_1407_ = v_isSharedCheck_1510_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1404_);
                        leanh::lean_dec(v___x_1403_);
                        v___x_1406_ = leanh::lean_box(0);
                        v_isShared_1407_ = v_isSharedCheck_1510_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1511_ = leanh::lean_ctor_get(v___x_1403_, 0);
                    v_isSharedCheck_1518_ = (!leanh::lean_is_exclusive(v___x_1403_)) as u8;
                    if v_isSharedCheck_1518_ == 0 {
                        v___x_1513_ = v___x_1403_;
                        v_isShared_1514_ = v_isSharedCheck_1518_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1511_);
                        leanh::lean_dec(v___x_1403_);
                        v___x_1513_ = leanh::lean_box(0);
                        v_isShared_1514_ = v_isSharedCheck_1518_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1413_ = l_Lean_Expr_cleanupAnnotations(v_a_1404_);
                v___x_1414_ = l_Lean_Expr_isApp(v___x_1413_);
                if v___x_1414_ == 0 {
                    leanh::lean_dec_ref(v___x_1413_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1415_ = leanh::lean_ctor_get(v___x_1413_, 1);
                    leanh::lean_inc_ref(v_arg_1415_);
                    v___x_1416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1413_);
                    v___x_1417_ = l_Lean_Expr_isApp(v___x_1416_);
                    if v___x_1417_ == 0 {
                        leanh::lean_dec_ref(v___x_1416_);
                        leanh::lean_dec_ref(v_arg_1415_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_1418_ = leanh::lean_ctor_get(v___x_1416_, 1);
                        leanh::lean_inc_ref(v_arg_1418_);
                        v___x_1419_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1416_);
                        v___x_1420_ = l_Lean_Expr_isApp(v___x_1419_);
                        if v___x_1420_ == 0 {
                            leanh::lean_dec_ref(v___x_1419_);
                            leanh::lean_dec_ref(v_arg_1418_);
                            leanh::lean_dec_ref(v_arg_1415_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_1421_ = leanh::lean_ctor_get(v___x_1419_, 1);
                            leanh::lean_inc_ref(v_arg_1421_);
                            v___x_1422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1419_);
                            v___x_1423_ = l_Lean_Expr_isApp(v___x_1422_);
                            if v___x_1423_ == 0 {
                                leanh::lean_dec_ref(v___x_1422_);
                                leanh::lean_dec_ref(v_arg_1421_);
                                leanh::lean_dec_ref(v_arg_1418_);
                                leanh::lean_dec_ref(v_arg_1415_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_1424_ = leanh::lean_ctor_get(v___x_1422_, 1);
                                leanh::lean_inc_ref(v_arg_1424_);
                                v___x_1425_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1422_);
                                v___x_1426_ = l_Lean_Expr_isApp(v___x_1425_);
                                if v___x_1426_ == 0 {
                                    leanh::lean_dec_ref(v___x_1425_);
                                    leanh::lean_dec_ref(v_arg_1424_);
                                    leanh::lean_dec_ref(v_arg_1421_);
                                    leanh::lean_dec_ref(v_arg_1418_);
                                    leanh::lean_dec_ref(v_arg_1415_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_1427_ = leanh::lean_ctor_get(v___x_1425_, 1);
                                    leanh::lean_inc_ref(v_arg_1427_);
                                    v___x_1428_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1425_);
                                    v___x_1429_ = l_reduceDIte___closed__1;
                                    v___x_1430_ = l_Lean_Expr_isConstOf(v___x_1428_, v___x_1429_);
                                    if v___x_1430_ == 0 {
                                        leanh::lean_dec_ref(v___x_1428_);
                                        leanh::lean_dec_ref(v_arg_1427_);
                                        leanh::lean_dec_ref(v_arg_1424_);
                                        leanh::lean_dec_ref(v_arg_1421_);
                                        leanh::lean_dec_ref(v_arg_1418_);
                                        leanh::lean_dec_ref(v_arg_1415_);
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_del_object(v___x_1406_);
                                        leanh::lean_inc(v_a_1401_);
                                        leanh::lean_inc_ref(v_a_1400_);
                                        leanh::lean_inc(v_a_1399_);
                                        leanh::lean_inc_ref(v_a_1398_);
                                        leanh::lean_inc(v_a_1397_);
                                        leanh::lean_inc_ref(v_a_1396_);
                                        leanh::lean_inc(v_a_1395_);
                                        leanh::lean_inc_ref(v_arg_1424_);
                                        v___x_1431_ = lean_simp(
                                            v_arg_1424_,
                                            v_a_1395_,
                                            v_a_1396_,
                                            v_a_1397_,
                                            v_a_1398_,
                                            v_a_1399_,
                                            v_a_1400_,
                                            v_a_1401_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1431_) == 0 {
                                            v_a_1432_ = leanh::lean_ctor_get(v___x_1431_, 0);
                                            v_isSharedCheck_1501_ =
                                                (!leanh::lean_is_exclusive(v___x_1431_))
                                                    as u8;
                                            if v_isSharedCheck_1501_ == 0 {
                                                v___x_1434_ = v___x_1431_;
                                                v_isShared_1435_ = v_isSharedCheck_1501_;
                                                state = 4;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1432_);
                                                leanh::lean_dec(v___x_1431_);
                                                v___x_1434_ = leanh::lean_box(0);
                                                v_isShared_1435_ = v_isSharedCheck_1501_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_1428_);
                                            leanh::lean_dec_ref(v_arg_1427_);
                                            leanh::lean_dec_ref(v_arg_1424_);
                                            leanh::lean_dec_ref(v_arg_1421_);
                                            leanh::lean_dec_ref(v_arg_1418_);
                                            leanh::lean_dec_ref(v_arg_1415_);
                                            v_a_1502_ = leanh::lean_ctor_get(v___x_1431_, 0);
                                            v_isSharedCheck_1509_ =
                                                (!leanh::lean_is_exclusive(v___x_1431_))
                                                    as u8;
                                            if v_isSharedCheck_1509_ == 0 {
                                                v___x_1504_ = v___x_1431_;
                                                v_isShared_1505_ = v_isSharedCheck_1509_;
                                                state = 14;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1502_);
                                                leanh::lean_dec(v___x_1431_);
                                                v___x_1504_ = leanh::lean_box(0);
                                                v_isShared_1505_ = v_isSharedCheck_1509_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1409_ = l_reduceIte___closed__0;
                if v_isShared_1407_ == 0 {
                    leanh::lean_ctor_set(v___x_1406_, 0, v___x_1409_);
                    v___x_1411_ = v___x_1406_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1411_;
            }
            4 => {
                v_expr_1436_ = leanh::lean_ctor_get(v_a_1432_, 0);
                leanh::lean_inc_ref(v_expr_1436_);
                v___x_1437_ = l_Lean_Expr_isTrue(v_expr_1436_);
                if v___x_1437_ == 0 {
                    leanh::lean_inc_ref(v_expr_1436_);
                    v___x_1438_ = l_Lean_Expr_isFalse(v_expr_1436_);
                    if v___x_1438_ == 0 {
                        leanh::lean_dec(v_a_1432_);
                        leanh::lean_dec_ref(v___x_1428_);
                        leanh::lean_dec_ref(v_arg_1427_);
                        leanh::lean_dec_ref(v_arg_1424_);
                        leanh::lean_dec_ref(v_arg_1421_);
                        leanh::lean_dec_ref(v_arg_1418_);
                        leanh::lean_dec_ref(v_arg_1415_);
                        v___x_1439_ = l_reduceIte___closed__0;
                        if v_isShared_1435_ == 0 {
                            leanh::lean_ctor_set(v___x_1434_, 0, v___x_1439_);
                            v___x_1441_ = v___x_1434_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1442_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
                            v___x_1441_ = v_reuseFailAlloc_1442_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1434_);
                        v___x_1443_ = l_Lean_Meta_Simp_Result_getProof(
                            v_a_1432_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_,
                        );
                        if leanh::lean_obj_tag(v___x_1443_) == 0 {
                            v_a_1444_ = leanh::lean_ctor_get(v___x_1443_, 0);
                            v_isSharedCheck_1463_ =
                                (!leanh::lean_is_exclusive(v___x_1443_)) as u8;
                            if v_isSharedCheck_1463_ == 0 {
                                v___x_1446_ = v___x_1443_;
                                v_isShared_1447_ = v_isSharedCheck_1463_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1444_);
                                leanh::lean_dec(v___x_1443_);
                                v___x_1446_ = leanh::lean_box(0);
                                v_isShared_1447_ = v_isSharedCheck_1463_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1428_);
                            leanh::lean_dec_ref(v_arg_1427_);
                            leanh::lean_dec_ref(v_arg_1424_);
                            leanh::lean_dec_ref(v_arg_1421_);
                            leanh::lean_dec_ref(v_arg_1418_);
                            leanh::lean_dec_ref(v_arg_1415_);
                            v_a_1464_ = leanh::lean_ctor_get(v___x_1443_, 0);
                            v_isSharedCheck_1471_ =
                                (!leanh::lean_is_exclusive(v___x_1443_)) as u8;
                            if v_isSharedCheck_1471_ == 0 {
                                v___x_1466_ = v___x_1443_;
                                v_isShared_1467_ = v_isSharedCheck_1471_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1464_);
                                leanh::lean_dec(v___x_1443_);
                                v___x_1466_ = leanh::lean_box(0);
                                v_isShared_1467_ = v_isSharedCheck_1471_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1434_);
                    v___x_1472_ = l_Lean_Meta_Simp_Result_getProof(
                        v_a_1432_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_,
                    );
                    if leanh::lean_obj_tag(v___x_1472_) == 0 {
                        v_a_1473_ = leanh::lean_ctor_get(v___x_1472_, 0);
                        v_isSharedCheck_1492_ =
                            (!leanh::lean_is_exclusive(v___x_1472_)) as u8;
                        if v_isSharedCheck_1492_ == 0 {
                            v___x_1475_ = v___x_1472_;
                            v_isShared_1476_ = v_isSharedCheck_1492_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1473_);
                            leanh::lean_dec(v___x_1472_);
                            v___x_1475_ = leanh::lean_box(0);
                            v_isShared_1476_ = v_isSharedCheck_1492_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1428_);
                        leanh::lean_dec_ref(v_arg_1427_);
                        leanh::lean_dec_ref(v_arg_1424_);
                        leanh::lean_dec_ref(v_arg_1421_);
                        leanh::lean_dec_ref(v_arg_1418_);
                        leanh::lean_dec_ref(v_arg_1415_);
                        v_a_1493_ = leanh::lean_ctor_get(v___x_1472_, 0);
                        v_isSharedCheck_1500_ =
                            (!leanh::lean_is_exclusive(v___x_1472_)) as u8;
                        if v_isSharedCheck_1500_ == 0 {
                            v___x_1495_ = v___x_1472_;
                            v_isShared_1496_ = v_isSharedCheck_1500_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1493_);
                            leanh::lean_dec(v___x_1472_);
                            v___x_1495_ = leanh::lean_box(0);
                            v_isShared_1496_ = v_isSharedCheck_1500_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_1441_;
            }
            6 => {
                v___x_1448_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__4),
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__4_once),
                    _init_l_reduceDIte___closed__4,
                );
                leanh::lean_inc(v_a_1444_);
                leanh::lean_inc_ref(v_arg_1424_);
                v___x_1449_ = l_Lean_mkAppB(v___x_1448_, v_arg_1424_, v_a_1444_);
                leanh::lean_inc_ref(v_arg_1415_);
                v___x_1450_ = l_Lean_Expr_app___override(v_arg_1415_, v___x_1449_);
                v___x_1451_ = l_Lean_Expr_headBeta(v___x_1450_);
                v___x_1452_ = l_reduceDIte___closed__6;
                v___x_1453_ = l_Lean_Expr_constLevels_x21(v___x_1428_);
                leanh::lean_dec_ref(v___x_1428_);
                v___x_1454_ = l_Lean_mkConst(v___x_1452_, v___x_1453_);
                v___x_1455_ = l_Lean_mkApp5(
                    v___x_1454_,
                    v_arg_1427_,
                    v_arg_1424_,
                    v_arg_1421_,
                    v_arg_1418_,
                    v_arg_1415_,
                );
                v___x_1456_ = l_Lean_Expr_app___override(v___x_1455_, v_a_1444_);
                v___x_1457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1457_, 0, v___x_1456_);
                v___x_1458_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1458_, 0, v___x_1451_);
                leanh::lean_ctor_set(v___x_1458_, 1, v___x_1457_);
                leanh::lean_ctor_set_uint8(
                    v___x_1458_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1430_,
                );
                v___x_1459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1459_, 0, v___x_1458_);
                if v_isShared_1447_ == 0 {
                    leanh::lean_ctor_set(v___x_1446_, 0, v___x_1459_);
                    v___x_1461_ = v___x_1446_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
                    v___x_1461_ = v_reuseFailAlloc_1462_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1461_;
            }
            8 => {
                if v_isShared_1467_ == 0 {
                    v___x_1469_ = v___x_1466_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
                    v___x_1469_ = v_reuseFailAlloc_1470_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1469_;
            }
            10 => {
                v___x_1477_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__9),
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__9_once),
                    _init_l_reduceDIte___closed__9,
                );
                leanh::lean_inc(v_a_1473_);
                leanh::lean_inc_ref(v_arg_1424_);
                v___x_1478_ = l_Lean_mkAppB(v___x_1477_, v_arg_1424_, v_a_1473_);
                leanh::lean_inc_ref(v_arg_1418_);
                v___x_1479_ = l_Lean_Expr_app___override(v_arg_1418_, v___x_1478_);
                v___x_1480_ = l_Lean_Expr_headBeta(v___x_1479_);
                v___x_1481_ = l_reduceDIte___closed__11;
                v___x_1482_ = l_Lean_Expr_constLevels_x21(v___x_1428_);
                leanh::lean_dec_ref(v___x_1428_);
                v___x_1483_ = l_Lean_mkConst(v___x_1481_, v___x_1482_);
                v___x_1484_ = l_Lean_mkApp5(
                    v___x_1483_,
                    v_arg_1427_,
                    v_arg_1424_,
                    v_arg_1421_,
                    v_arg_1418_,
                    v_arg_1415_,
                );
                v___x_1485_ = l_Lean_Expr_app___override(v___x_1484_, v_a_1473_);
                v___x_1486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                v___x_1487_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1487_, 0, v___x_1480_);
                leanh::lean_ctor_set(v___x_1487_, 1, v___x_1486_);
                leanh::lean_ctor_set_uint8(
                    v___x_1487_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1430_,
                );
                v___x_1488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1488_, 0, v___x_1487_);
                if v_isShared_1476_ == 0 {
                    leanh::lean_ctor_set(v___x_1475_, 0, v___x_1488_);
                    v___x_1490_ = v___x_1475_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
                    v___x_1490_ = v_reuseFailAlloc_1491_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1490_;
            }
            12 => {
                if v_isShared_1496_ == 0 {
                    v___x_1498_ = v___x_1495_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1499_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
                    v___x_1498_ = v_reuseFailAlloc_1499_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1498_;
            }
            14 => {
                if v_isShared_1505_ == 0 {
                    v___x_1507_ = v___x_1504_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
                    v___x_1507_ = v_reuseFailAlloc_1508_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1507_;
            }
            16 => {
                if v_isShared_1514_ == 0 {
                    v___x_1516_ = v___x_1513_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
                    v___x_1516_ = v_reuseFailAlloc_1517_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_reduceDIte___boxed(
    mut v_e_1519_: *mut leanh::LeanObject,
    mut v_a_1520_: *mut leanh::LeanObject,
    mut v_a_1521_: *mut leanh::LeanObject,
    mut v_a_1522_: *mut leanh::LeanObject,
    mut v_a_1523_: *mut leanh::LeanObject,
    mut v_a_1524_: *mut leanh::LeanObject,
    mut v_a_1525_: *mut leanh::LeanObject,
    mut v_a_1526_: *mut leanh::LeanObject,
    mut v_a_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1528_ = l_reduceDIte(
        v_e_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_,
    );
    leanh::lean_dec(v_a_1526_);
    leanh::lean_dec_ref(v_a_1525_);
    leanh::lean_dec(v_a_1524_);
    leanh::lean_dec_ref(v_a_1523_);
    leanh::lean_dec(v_a_1522_);
    leanh::lean_dec_ref(v_a_1521_);
    leanh::lean_dec(v_a_1520_);
    return v_res_1528_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1547_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1548_ =
        leanh::lean_alloc_closure(l_reduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1549_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1546_, v___x_1547_, v___x_1548_);
    return v___x_1549_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15____boxed(
    mut v_a_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
    return v_res_1551_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ =
        leanh::lean_alloc_closure(l_reduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1553_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1553_, 0, v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1556_ = 0;
    v___x_1557_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
    v___x_1558_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1555_, v___x_1556_, v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(
    mut v_a_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
    return v_res_1560_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_()
-> *mut leanh::LeanObject {
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1563_ = 0;
    v___x_1564_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
    v___x_1565_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1562_, v___x_1563_, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(
    mut v_a_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1567_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
    return v_res_1567_;
}
pub unsafe fn l_dreduceIte(
    mut v_e_1579_: *mut leanh::LeanObject,
    mut v_a_1580_: *mut leanh::LeanObject,
    mut v_a_1581_: *mut leanh::LeanObject,
    mut v_a_1582_: *mut leanh::LeanObject,
    mut v_a_1583_: *mut leanh::LeanObject,
    mut v_a_1584_: *mut leanh::LeanObject,
    mut v_a_1585_: *mut leanh::LeanObject,
    mut v_a_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inDSimp_1591_: u8 = 0;
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1598_: u8 = 0;
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v_arg_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v_arg_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v_arg_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v_arg_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_a_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v_a_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_expr_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut v_a_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_a_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inDSimp_1591_ = leanh::lean_ctor_get_uint8(
                    v_a_1581_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 8) as u32,
                );
                if v_inDSimp_1591_ == 0 {
                    leanh::lean_dec_ref(v_e_1579_);
                    v___x_1592_ = l_dreduceIte___closed__0;
                    v___x_1593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1593_, 0, v___x_1592_);
                    return v___x_1593_;
                } else {
                    v___x_1594_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1579_, v_a_1584_);
                    if leanh::lean_obj_tag(v___x_1594_) == 0 {
                        v_a_1595_ = leanh::lean_ctor_get(v___x_1594_, 0);
                        v_isSharedCheck_1684_ =
                            (!leanh::lean_is_exclusive(v___x_1594_)) as u8;
                        if v_isSharedCheck_1684_ == 0 {
                            v___x_1597_ = v___x_1594_;
                            v_isShared_1598_ = v_isSharedCheck_1684_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1595_);
                            leanh::lean_dec(v___x_1594_);
                            v___x_1597_ = leanh::lean_box(0);
                            v_isShared_1598_ = v_isSharedCheck_1684_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1685_ = leanh::lean_ctor_get(v___x_1594_, 0);
                        v_isSharedCheck_1692_ =
                            (!leanh::lean_is_exclusive(v___x_1594_)) as u8;
                        if v_isSharedCheck_1692_ == 0 {
                            v___x_1687_ = v___x_1594_;
                            v_isShared_1688_ = v_isSharedCheck_1692_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1685_);
                            leanh::lean_dec(v___x_1594_);
                            v___x_1687_ = leanh::lean_box(0);
                            v_isShared_1688_ = v_isSharedCheck_1692_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1589_ = l_dreduceIte___closed__0;
                v___x_1590_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1590_, 0, v___x_1589_);
                return v___x_1590_;
            }
            2 => {
                v___x_1604_ = l_Lean_Expr_cleanupAnnotations(v_a_1595_);
                v___x_1605_ = l_Lean_Expr_isApp(v___x_1604_);
                if v___x_1605_ == 0 {
                    leanh::lean_dec_ref(v___x_1604_);
                    state = 3;
                    continue;
                } else {
                    v_arg_1606_ = leanh::lean_ctor_get(v___x_1604_, 1);
                    leanh::lean_inc_ref(v_arg_1606_);
                    v___x_1607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1604_);
                    v___x_1608_ = l_Lean_Expr_isApp(v___x_1607_);
                    if v___x_1608_ == 0 {
                        leanh::lean_dec_ref(v___x_1607_);
                        leanh::lean_dec_ref(v_arg_1606_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_1609_ = leanh::lean_ctor_get(v___x_1607_, 1);
                        leanh::lean_inc_ref(v_arg_1609_);
                        v___x_1610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1607_);
                        v___x_1611_ = l_Lean_Expr_isApp(v___x_1610_);
                        if v___x_1611_ == 0 {
                            leanh::lean_dec_ref(v___x_1610_);
                            leanh::lean_dec_ref(v_arg_1609_);
                            leanh::lean_dec_ref(v_arg_1606_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_1612_ = leanh::lean_ctor_get(v___x_1610_, 1);
                            leanh::lean_inc_ref(v_arg_1612_);
                            v___x_1613_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1610_);
                            v___x_1614_ = l_Lean_Expr_isApp(v___x_1613_);
                            if v___x_1614_ == 0 {
                                leanh::lean_dec_ref(v___x_1613_);
                                leanh::lean_dec_ref(v_arg_1612_);
                                leanh::lean_dec_ref(v_arg_1609_);
                                leanh::lean_dec_ref(v_arg_1606_);
                                state = 3;
                                continue;
                            } else {
                                v_arg_1615_ = leanh::lean_ctor_get(v___x_1613_, 1);
                                leanh::lean_inc_ref(v_arg_1615_);
                                v___x_1616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1613_);
                                v___x_1617_ = l_Lean_Expr_isApp(v___x_1616_);
                                if v___x_1617_ == 0 {
                                    leanh::lean_dec_ref(v___x_1616_);
                                    leanh::lean_dec_ref(v_arg_1615_);
                                    leanh::lean_dec_ref(v_arg_1612_);
                                    leanh::lean_dec_ref(v_arg_1609_);
                                    leanh::lean_dec_ref(v_arg_1606_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_1618_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1616_);
                                    v___x_1619_ = l_reduceIte___closed__2;
                                    v___x_1620_ = l_Lean_Expr_isConstOf(v___x_1618_, v___x_1619_);
                                    leanh::lean_dec_ref(v___x_1618_);
                                    if v___x_1620_ == 0 {
                                        leanh::lean_dec_ref(v_arg_1615_);
                                        leanh::lean_dec_ref(v_arg_1612_);
                                        leanh::lean_dec_ref(v_arg_1609_);
                                        leanh::lean_dec_ref(v_arg_1606_);
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_del_object(v___x_1597_);
                                        leanh::lean_inc(v_a_1586_);
                                        leanh::lean_inc_ref(v_a_1585_);
                                        leanh::lean_inc(v_a_1584_);
                                        leanh::lean_inc_ref(v_a_1583_);
                                        leanh::lean_inc(v_a_1582_);
                                        leanh::lean_inc_ref(v_a_1581_);
                                        leanh::lean_inc(v_a_1580_);
                                        v___x_1621_ = lean_simp(
                                            v_arg_1615_,
                                            v_a_1580_,
                                            v_a_1581_,
                                            v_a_1582_,
                                            v_a_1583_,
                                            v_a_1584_,
                                            v_a_1585_,
                                            v_a_1586_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1621_) == 0 {
                                            v_a_1622_ = leanh::lean_ctor_get(v___x_1621_, 0);
                                            v_isSharedCheck_1675_ =
                                                (!leanh::lean_is_exclusive(v___x_1621_))
                                                    as u8;
                                            if v_isSharedCheck_1675_ == 0 {
                                                v___x_1624_ = v___x_1621_;
                                                v_isShared_1625_ = v_isSharedCheck_1675_;
                                                state = 5;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1622_);
                                                leanh::lean_dec(v___x_1621_);
                                                v___x_1624_ = leanh::lean_box(0);
                                                v_isShared_1625_ = v_isSharedCheck_1675_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_1612_);
                                            leanh::lean_dec_ref(v_arg_1609_);
                                            leanh::lean_dec_ref(v_arg_1606_);
                                            v_a_1676_ = leanh::lean_ctor_get(v___x_1621_, 0);
                                            v_isSharedCheck_1683_ =
                                                (!leanh::lean_is_exclusive(v___x_1621_))
                                                    as u8;
                                            if v_isSharedCheck_1683_ == 0 {
                                                v___x_1678_ = v___x_1621_;
                                                v_isShared_1679_ = v_isSharedCheck_1683_;
                                                state = 15;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1676_);
                                                leanh::lean_dec(v___x_1621_);
                                                v___x_1678_ = leanh::lean_box(0);
                                                v_isShared_1679_ = v_isSharedCheck_1683_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_1600_ = l_dreduceIte___closed__0;
                if v_isShared_1598_ == 0 {
                    leanh::lean_ctor_set(v___x_1597_, 0, v___x_1600_);
                    v___x_1602_ = v___x_1597_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
                    v___x_1602_ = v_reuseFailAlloc_1603_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1602_;
            }
            5 => {
                v_expr_1668_ = leanh::lean_ctor_get(v_a_1622_, 0);
                leanh::lean_inc_ref_n(v_expr_1668_, 2);
                leanh::lean_dec(v_a_1622_);
                v___x_1669_ = l_Lean_Expr_isTrue(v_expr_1668_);
                if v___x_1669_ == 0 {
                    v___x_1670_ = l_Lean_Expr_isFalse(v_expr_1668_);
                    if v___x_1670_ == 0 {
                        leanh::lean_dec_ref(v_arg_1612_);
                        leanh::lean_dec_ref(v_arg_1609_);
                        leanh::lean_dec_ref(v_arg_1606_);
                        v___x_1671_ = l_dreduceIte___closed__0;
                        if v_isShared_1625_ == 0 {
                            leanh::lean_ctor_set(v___x_1624_, 0, v___x_1671_);
                            v___x_1673_ = v___x_1624_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1674_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
                            v___x_1673_ = v_reuseFailAlloc_1674_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1624_);
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_expr_1668_);
                    leanh::lean_del_object(v___x_1624_);
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1627_ =
                    l_Lean_Meta_whnfD(v_arg_1612_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
                if leanh::lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = leanh::lean_ctor_get(v___x_1627_, 0);
                    leanh::lean_inc(v_a_1628_);
                    leanh::lean_dec_ref_known(v___x_1627_, 1);
                    v___x_1629_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_1628_, v_a_1584_);
                    if leanh::lean_obj_tag(v___x_1629_) == 0 {
                        v_a_1630_ = leanh::lean_ctor_get(v___x_1629_, 0);
                        v_isSharedCheck_1651_ =
                            (!leanh::lean_is_exclusive(v___x_1629_)) as u8;
                        if v_isSharedCheck_1651_ == 0 {
                            v___x_1632_ = v___x_1629_;
                            v_isShared_1633_ = v_isSharedCheck_1651_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1630_);
                            leanh::lean_dec(v___x_1629_);
                            v___x_1632_ = leanh::lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1651_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1609_);
                        leanh::lean_dec_ref(v_arg_1606_);
                        v_a_1652_ = leanh::lean_ctor_get(v___x_1629_, 0);
                        v_isSharedCheck_1659_ =
                            (!leanh::lean_is_exclusive(v___x_1629_)) as u8;
                        if v_isSharedCheck_1659_ == 0 {
                            v___x_1654_ = v___x_1629_;
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1652_);
                            leanh::lean_dec(v___x_1629_);
                            v___x_1654_ = leanh::lean_box(0);
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_1609_);
                    leanh::lean_dec_ref(v_arg_1606_);
                    v_a_1660_ = leanh::lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1667_ = (!leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1662_ = v___x_1627_;
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1660_);
                        leanh::lean_dec(v___x_1627_);
                        v___x_1662_ = leanh::lean_box(0);
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1634_ = l_Lean_Expr_cleanupAnnotations(v_a_1630_);
                v___x_1635_ = l_Lean_Expr_isApp(v___x_1634_);
                if v___x_1635_ == 0 {
                    leanh::lean_dec_ref(v___x_1634_);
                    leanh::lean_del_object(v___x_1632_);
                    leanh::lean_dec_ref(v_arg_1609_);
                    leanh::lean_dec_ref(v_arg_1606_);
                    state = 1;
                    continue;
                } else {
                    v___x_1636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1634_);
                    v___x_1637_ = l_Lean_Expr_isApp(v___x_1636_);
                    if v___x_1637_ == 0 {
                        leanh::lean_dec_ref(v___x_1636_);
                        leanh::lean_del_object(v___x_1632_);
                        leanh::lean_dec_ref(v_arg_1609_);
                        leanh::lean_dec_ref(v_arg_1606_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1636_);
                        v___x_1639_ = l_dreduceIte___closed__3;
                        v___x_1640_ = l_Lean_Expr_isConstOf(v___x_1638_, v___x_1639_);
                        if v___x_1640_ == 0 {
                            leanh::lean_dec_ref(v_arg_1606_);
                            v___x_1641_ = l_dreduceIte___closed__5;
                            v___x_1642_ = l_Lean_Expr_isConstOf(v___x_1638_, v___x_1641_);
                            leanh::lean_dec_ref(v___x_1638_);
                            if v___x_1642_ == 0 {
                                leanh::lean_del_object(v___x_1632_);
                                leanh::lean_dec_ref(v_arg_1609_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1643_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1643_, 0, v_arg_1609_);
                                if v_isShared_1633_ == 0 {
                                    leanh::lean_ctor_set(v___x_1632_, 0, v___x_1643_);
                                    v___x_1645_ = v___x_1632_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1646_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1646_,
                                        0,
                                        v___x_1643_,
                                    );
                                    v___x_1645_ = v_reuseFailAlloc_1646_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1638_);
                            leanh::lean_dec_ref(v_arg_1609_);
                            v___x_1647_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1647_, 0, v_arg_1606_);
                            if v_isShared_1633_ == 0 {
                                leanh::lean_ctor_set(v___x_1632_, 0, v___x_1647_);
                                v___x_1649_ = v___x_1632_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1650_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
                                v___x_1649_ = v_reuseFailAlloc_1650_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                return v___x_1645_;
            }
            9 => {
                return v___x_1649_;
            }
            10 => {
                if v_isShared_1655_ == 0 {
                    v___x_1657_ = v___x_1654_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
                    v___x_1657_ = v_reuseFailAlloc_1658_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1657_;
            }
            12 => {
                if v_isShared_1663_ == 0 {
                    v___x_1665_ = v___x_1662_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
                    v___x_1665_ = v_reuseFailAlloc_1666_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1665_;
            }
            14 => {
                return v___x_1673_;
            }
            15 => {
                if v_isShared_1679_ == 0 {
                    v___x_1681_ = v___x_1678_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
                    v___x_1681_ = v_reuseFailAlloc_1682_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1681_;
            }
            17 => {
                if v_isShared_1688_ == 0 {
                    v___x_1690_ = v___x_1687_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1691_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
                    v___x_1690_ = v_reuseFailAlloc_1691_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_dreduceIte___boxed(
    mut v_e_1693_: *mut leanh::LeanObject,
    mut v_a_1694_: *mut leanh::LeanObject,
    mut v_a_1695_: *mut leanh::LeanObject,
    mut v_a_1696_: *mut leanh::LeanObject,
    mut v_a_1697_: *mut leanh::LeanObject,
    mut v_a_1698_: *mut leanh::LeanObject,
    mut v_a_1699_: *mut leanh::LeanObject,
    mut v_a_1700_: *mut leanh::LeanObject,
    mut v_a_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_dreduceIte(
        v_e_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_,
    );
    leanh::lean_dec(v_a_1700_);
    leanh::lean_dec_ref(v_a_1699_);
    leanh::lean_dec(v_a_1698_);
    leanh::lean_dec_ref(v_a_1697_);
    leanh::lean_dec(v_a_1696_);
    leanh::lean_dec_ref(v_a_1695_);
    leanh::lean_dec(v_a_1694_);
    return v_res_1702_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_;
    v___x_1708_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1709_ =
        leanh::lean_alloc_closure(l_dreduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1710_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1707_, v___x_1708_, v___x_1709_);
    return v___x_1710_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15____boxed(
    mut v_a_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
    return v_res_1712_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ =
        leanh::lean_alloc_closure(l_dreduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1714_, 0, v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_;
    v___x_1717_ = 0;
    v___x_1718_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
    v___x_1719_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1716_, v___x_1717_, v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17____boxed(
    mut v_a_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
    return v_res_1721_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_()
-> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_;
    v___x_1724_ = 0;
    v___x_1725_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
    v___x_1726_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1723_, v___x_1724_, v___x_1725_);
    return v___x_1726_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19____boxed(
    mut v_a_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1728_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
    return v_res_1728_;
}
pub unsafe fn l_dreduceDIte(
    mut v_e_1729_: *mut leanh::LeanObject,
    mut v_a_1730_: *mut leanh::LeanObject,
    mut v_a_1731_: *mut leanh::LeanObject,
    mut v_a_1732_: *mut leanh::LeanObject,
    mut v_a_1733_: *mut leanh::LeanObject,
    mut v_a_1734_: *mut leanh::LeanObject,
    mut v_a_1735_: *mut leanh::LeanObject,
    mut v_a_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inDSimp_1741_: u8 = 0;
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v_arg_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v_arg_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v_arg_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v_arg_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v_arg_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_a_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut v_a_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v_expr_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v_a_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_a_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inDSimp_1741_ = leanh::lean_ctor_get_uint8(
                    v_a_1731_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 8) as u32,
                );
                if v_inDSimp_1741_ == 0 {
                    leanh::lean_dec_ref(v_e_1729_);
                    v___x_1742_ = l_dreduceIte___closed__0;
                    v___x_1743_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    return v___x_1743_;
                } else {
                    v___x_1744_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1729_, v_a_1734_);
                    if leanh::lean_obj_tag(v___x_1744_) == 0 {
                        v_a_1745_ = leanh::lean_ctor_get(v___x_1744_, 0);
                        v_isSharedCheck_1839_ =
                            (!leanh::lean_is_exclusive(v___x_1744_)) as u8;
                        if v_isSharedCheck_1839_ == 0 {
                            v___x_1747_ = v___x_1744_;
                            v_isShared_1748_ = v_isSharedCheck_1839_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1745_);
                            leanh::lean_dec(v___x_1744_);
                            v___x_1747_ = leanh::lean_box(0);
                            v_isShared_1748_ = v_isSharedCheck_1839_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1840_ = leanh::lean_ctor_get(v___x_1744_, 0);
                        v_isSharedCheck_1847_ =
                            (!leanh::lean_is_exclusive(v___x_1744_)) as u8;
                        if v_isSharedCheck_1847_ == 0 {
                            v___x_1842_ = v___x_1744_;
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1840_);
                            leanh::lean_dec(v___x_1744_);
                            v___x_1842_ = leanh::lean_box(0);
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1739_ = l_dreduceIte___closed__0;
                v___x_1740_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
                return v___x_1740_;
            }
            2 => {
                v___x_1754_ = l_Lean_Expr_cleanupAnnotations(v_a_1745_);
                v___x_1755_ = l_Lean_Expr_isApp(v___x_1754_);
                if v___x_1755_ == 0 {
                    leanh::lean_dec_ref(v___x_1754_);
                    state = 3;
                    continue;
                } else {
                    v_arg_1756_ = leanh::lean_ctor_get(v___x_1754_, 1);
                    leanh::lean_inc_ref(v_arg_1756_);
                    v___x_1757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1754_);
                    v___x_1758_ = l_Lean_Expr_isApp(v___x_1757_);
                    if v___x_1758_ == 0 {
                        leanh::lean_dec_ref(v___x_1757_);
                        leanh::lean_dec_ref(v_arg_1756_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_1759_ = leanh::lean_ctor_get(v___x_1757_, 1);
                        leanh::lean_inc_ref(v_arg_1759_);
                        v___x_1760_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1757_);
                        v___x_1761_ = l_Lean_Expr_isApp(v___x_1760_);
                        if v___x_1761_ == 0 {
                            leanh::lean_dec_ref(v___x_1760_);
                            leanh::lean_dec_ref(v_arg_1759_);
                            leanh::lean_dec_ref(v_arg_1756_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_1762_ = leanh::lean_ctor_get(v___x_1760_, 1);
                            leanh::lean_inc_ref(v_arg_1762_);
                            v___x_1763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1760_);
                            v___x_1764_ = l_Lean_Expr_isApp(v___x_1763_);
                            if v___x_1764_ == 0 {
                                leanh::lean_dec_ref(v___x_1763_);
                                leanh::lean_dec_ref(v_arg_1762_);
                                leanh::lean_dec_ref(v_arg_1759_);
                                leanh::lean_dec_ref(v_arg_1756_);
                                state = 3;
                                continue;
                            } else {
                                v_arg_1765_ = leanh::lean_ctor_get(v___x_1763_, 1);
                                leanh::lean_inc_ref(v_arg_1765_);
                                v___x_1766_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1763_);
                                v___x_1767_ = l_Lean_Expr_isApp(v___x_1766_);
                                if v___x_1767_ == 0 {
                                    leanh::lean_dec_ref(v___x_1766_);
                                    leanh::lean_dec_ref(v_arg_1765_);
                                    leanh::lean_dec_ref(v_arg_1762_);
                                    leanh::lean_dec_ref(v_arg_1759_);
                                    leanh::lean_dec_ref(v_arg_1756_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_1768_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1766_);
                                    v___x_1769_ = l_reduceDIte___closed__1;
                                    v___x_1770_ = l_Lean_Expr_isConstOf(v___x_1768_, v___x_1769_);
                                    leanh::lean_dec_ref(v___x_1768_);
                                    if v___x_1770_ == 0 {
                                        leanh::lean_dec_ref(v_arg_1765_);
                                        leanh::lean_dec_ref(v_arg_1762_);
                                        leanh::lean_dec_ref(v_arg_1759_);
                                        leanh::lean_dec_ref(v_arg_1756_);
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_del_object(v___x_1747_);
                                        leanh::lean_inc(v_a_1736_);
                                        leanh::lean_inc_ref(v_a_1735_);
                                        leanh::lean_inc(v_a_1734_);
                                        leanh::lean_inc_ref(v_a_1733_);
                                        leanh::lean_inc(v_a_1732_);
                                        leanh::lean_inc_ref(v_a_1731_);
                                        leanh::lean_inc(v_a_1730_);
                                        v___x_1771_ = lean_simp(
                                            v_arg_1765_,
                                            v_a_1730_,
                                            v_a_1731_,
                                            v_a_1732_,
                                            v_a_1733_,
                                            v_a_1734_,
                                            v_a_1735_,
                                            v_a_1736_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1771_) == 0 {
                                            v_a_1772_ = leanh::lean_ctor_get(v___x_1771_, 0);
                                            v_isSharedCheck_1830_ =
                                                (!leanh::lean_is_exclusive(v___x_1771_))
                                                    as u8;
                                            if v_isSharedCheck_1830_ == 0 {
                                                v___x_1774_ = v___x_1771_;
                                                v_isShared_1775_ = v_isSharedCheck_1830_;
                                                state = 5;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1772_);
                                                leanh::lean_dec(v___x_1771_);
                                                v___x_1774_ = leanh::lean_box(0);
                                                v_isShared_1775_ = v_isSharedCheck_1830_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_1762_);
                                            leanh::lean_dec_ref(v_arg_1759_);
                                            leanh::lean_dec_ref(v_arg_1756_);
                                            v_a_1831_ = leanh::lean_ctor_get(v___x_1771_, 0);
                                            v_isSharedCheck_1838_ =
                                                (!leanh::lean_is_exclusive(v___x_1771_))
                                                    as u8;
                                            if v_isSharedCheck_1838_ == 0 {
                                                v___x_1833_ = v___x_1771_;
                                                v_isShared_1834_ = v_isSharedCheck_1838_;
                                                state = 15;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1831_);
                                                leanh::lean_dec(v___x_1771_);
                                                v___x_1833_ = leanh::lean_box(0);
                                                v_isShared_1834_ = v_isSharedCheck_1838_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_1750_ = l_dreduceIte___closed__0;
                if v_isShared_1748_ == 0 {
                    leanh::lean_ctor_set(v___x_1747_, 0, v___x_1750_);
                    v___x_1752_ = v___x_1747_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1752_;
            }
            5 => {
                v_expr_1823_ = leanh::lean_ctor_get(v_a_1772_, 0);
                leanh::lean_inc_ref_n(v_expr_1823_, 2);
                leanh::lean_dec(v_a_1772_);
                v___x_1824_ = l_Lean_Expr_isTrue(v_expr_1823_);
                if v___x_1824_ == 0 {
                    v___x_1825_ = l_Lean_Expr_isFalse(v_expr_1823_);
                    if v___x_1825_ == 0 {
                        leanh::lean_dec_ref(v_arg_1762_);
                        leanh::lean_dec_ref(v_arg_1759_);
                        leanh::lean_dec_ref(v_arg_1756_);
                        v___x_1826_ = l_dreduceIte___closed__0;
                        if v_isShared_1775_ == 0 {
                            leanh::lean_ctor_set(v___x_1774_, 0, v___x_1826_);
                            v___x_1828_ = v___x_1774_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1829_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
                            v___x_1828_ = v_reuseFailAlloc_1829_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1774_);
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_expr_1823_);
                    leanh::lean_del_object(v___x_1774_);
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1777_ =
                    l_Lean_Meta_whnfD(v_arg_1762_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
                if leanh::lean_obj_tag(v___x_1777_) == 0 {
                    v_a_1778_ = leanh::lean_ctor_get(v___x_1777_, 0);
                    leanh::lean_inc(v_a_1778_);
                    leanh::lean_dec_ref_known(v___x_1777_, 1);
                    v___x_1779_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_1778_, v_a_1734_);
                    if leanh::lean_obj_tag(v___x_1779_) == 0 {
                        v_a_1780_ = leanh::lean_ctor_get(v___x_1779_, 0);
                        v_isSharedCheck_1806_ =
                            (!leanh::lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1806_ == 0 {
                            v___x_1782_ = v___x_1779_;
                            v_isShared_1783_ = v_isSharedCheck_1806_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1780_);
                            leanh::lean_dec(v___x_1779_);
                            v___x_1782_ = leanh::lean_box(0);
                            v_isShared_1783_ = v_isSharedCheck_1806_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1759_);
                        leanh::lean_dec_ref(v_arg_1756_);
                        v_a_1807_ = leanh::lean_ctor_get(v___x_1779_, 0);
                        v_isSharedCheck_1814_ =
                            (!leanh::lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1814_ == 0 {
                            v___x_1809_ = v___x_1779_;
                            v_isShared_1810_ = v_isSharedCheck_1814_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1807_);
                            leanh::lean_dec(v___x_1779_);
                            v___x_1809_ = leanh::lean_box(0);
                            v_isShared_1810_ = v_isSharedCheck_1814_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_1759_);
                    leanh::lean_dec_ref(v_arg_1756_);
                    v_a_1815_ = leanh::lean_ctor_get(v___x_1777_, 0);
                    v_isSharedCheck_1822_ = (!leanh::lean_is_exclusive(v___x_1777_)) as u8;
                    if v_isSharedCheck_1822_ == 0 {
                        v___x_1817_ = v___x_1777_;
                        v_isShared_1818_ = v_isSharedCheck_1822_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1815_);
                        leanh::lean_dec(v___x_1777_);
                        v___x_1817_ = leanh::lean_box(0);
                        v_isShared_1818_ = v_isSharedCheck_1822_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1784_ = l_Lean_Expr_cleanupAnnotations(v_a_1780_);
                v___x_1785_ = l_Lean_Expr_isApp(v___x_1784_);
                if v___x_1785_ == 0 {
                    leanh::lean_dec_ref(v___x_1784_);
                    leanh::lean_del_object(v___x_1782_);
                    leanh::lean_dec_ref(v_arg_1759_);
                    leanh::lean_dec_ref(v_arg_1756_);
                    state = 1;
                    continue;
                } else {
                    v_arg_1786_ = leanh::lean_ctor_get(v___x_1784_, 1);
                    leanh::lean_inc_ref(v_arg_1786_);
                    v___x_1787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1784_);
                    v___x_1788_ = l_Lean_Expr_isApp(v___x_1787_);
                    if v___x_1788_ == 0 {
                        leanh::lean_dec_ref(v___x_1787_);
                        leanh::lean_dec_ref(v_arg_1786_);
                        leanh::lean_del_object(v___x_1782_);
                        leanh::lean_dec_ref(v_arg_1759_);
                        leanh::lean_dec_ref(v_arg_1756_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1787_);
                        v___x_1790_ = l_dreduceIte___closed__3;
                        v___x_1791_ = l_Lean_Expr_isConstOf(v___x_1789_, v___x_1790_);
                        if v___x_1791_ == 0 {
                            leanh::lean_dec_ref(v_arg_1756_);
                            v___x_1792_ = l_dreduceIte___closed__5;
                            v___x_1793_ = l_Lean_Expr_isConstOf(v___x_1789_, v___x_1792_);
                            leanh::lean_dec_ref(v___x_1789_);
                            if v___x_1793_ == 0 {
                                leanh::lean_dec_ref(v_arg_1786_);
                                leanh::lean_del_object(v___x_1782_);
                                leanh::lean_dec_ref(v_arg_1759_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1794_ = l_Lean_Expr_app___override(v_arg_1759_, v_arg_1786_);
                                v___x_1795_ = l_Lean_Expr_headBeta(v___x_1794_);
                                v___x_1796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1796_, 0, v___x_1795_);
                                if v_isShared_1783_ == 0 {
                                    leanh::lean_ctor_set(v___x_1782_, 0, v___x_1796_);
                                    v___x_1798_ = v___x_1782_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1799_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1799_,
                                        0,
                                        v___x_1796_,
                                    );
                                    v___x_1798_ = v_reuseFailAlloc_1799_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1789_);
                            leanh::lean_dec_ref(v_arg_1759_);
                            v___x_1800_ = l_Lean_Expr_app___override(v_arg_1756_, v_arg_1786_);
                            v___x_1801_ = l_Lean_Expr_headBeta(v___x_1800_);
                            v___x_1802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1802_, 0, v___x_1801_);
                            if v_isShared_1783_ == 0 {
                                leanh::lean_ctor_set(v___x_1782_, 0, v___x_1802_);
                                v___x_1804_ = v___x_1782_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1805_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
                                v___x_1804_ = v_reuseFailAlloc_1805_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                return v___x_1798_;
            }
            9 => {
                return v___x_1804_;
            }
            10 => {
                if v_isShared_1810_ == 0 {
                    v___x_1812_ = v___x_1809_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1812_;
            }
            12 => {
                if v_isShared_1818_ == 0 {
                    v___x_1820_ = v___x_1817_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
                    v___x_1820_ = v_reuseFailAlloc_1821_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1820_;
            }
            14 => {
                return v___x_1828_;
            }
            15 => {
                if v_isShared_1834_ == 0 {
                    v___x_1836_ = v___x_1833_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
                    v___x_1836_ = v_reuseFailAlloc_1837_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1836_;
            }
            17 => {
                if v_isShared_1843_ == 0 {
                    v___x_1845_ = v___x_1842_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1846_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
                    v___x_1845_ = v_reuseFailAlloc_1846_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_dreduceDIte___boxed(
    mut v_e_1848_: *mut leanh::LeanObject,
    mut v_a_1849_: *mut leanh::LeanObject,
    mut v_a_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
    mut v_a_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_dreduceDIte(
        v_e_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_,
    );
    leanh::lean_dec(v_a_1855_);
    leanh::lean_dec_ref(v_a_1854_);
    leanh::lean_dec(v_a_1853_);
    leanh::lean_dec_ref(v_a_1852_);
    leanh::lean_dec(v_a_1851_);
    leanh::lean_dec_ref(v_a_1850_);
    leanh::lean_dec(v_a_1849_);
    return v_res_1857_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_;
    v___x_1863_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1864_ =
        leanh::lean_alloc_closure(l_dreduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1865_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1862_, v___x_1863_, v___x_1864_);
    return v___x_1865_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15____boxed(
    mut v_a_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
    return v_res_1867_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ =
        leanh::lean_alloc_closure(l_dreduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1869_, 0, v___x_1868_);
    return v___x_1869_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: u8 = 0;
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_;
    v___x_1872_ = 0;
    v___x_1873_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
    v___x_1874_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1871_, v___x_1872_, v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17____boxed(
    mut v_a_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
    return v_res_1876_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_()
-> *mut leanh::LeanObject {
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1878_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_;
    v___x_1879_ = 0;
    v___x_1880_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
    v___x_1881_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1878_, v___x_1879_, v___x_1880_);
    return v___x_1881_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19____boxed(
    mut v_a_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
    return v_res_1883_;
}
pub unsafe fn l_reduceCtorEq___lam__0(
    mut v_x_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = l_reduceIte___closed__0;
    v___x_1894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1894_, 0, v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn l_reduceCtorEq___lam__0___boxed(
    mut v_x_1895_: *mut leanh::LeanObject,
    mut v___y_1896_: *mut leanh::LeanObject,
    mut v___y_1897_: *mut leanh::LeanObject,
    mut v___y_1898_: *mut leanh::LeanObject,
    mut v___y_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
    mut v___y_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l_reduceCtorEq___lam__0(
        v_x_1895_,
        v___y_1896_,
        v___y_1897_,
        v___y_1898_,
        v___y_1899_,
        v___y_1900_,
        v___y_1901_,
        v___y_1902_,
    );
    leanh::lean_dec(v___y_1902_);
    leanh::lean_dec_ref(v___y_1901_);
    leanh::lean_dec(v___y_1900_);
    leanh::lean_dec_ref(v___y_1899_);
    leanh::lean_dec(v___y_1898_);
    leanh::lean_dec_ref(v___y_1897_);
    leanh::lean_dec(v___y_1896_);
    return v_res_1904_;
}
pub unsafe fn l_reduceCtorEq___lam__1(
    mut v_x_1905_: *mut leanh::LeanObject,
    mut v_x_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
    mut v___y_1909_: *mut leanh::LeanObject,
    mut v___y_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_reduceIte___closed__0;
    v___x_1916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1916_, 0, v___x_1915_);
    return v___x_1916_;
}
pub unsafe fn l_reduceCtorEq___lam__1___boxed(
    mut v_x_1917_: *mut leanh::LeanObject,
    mut v_x_1918_: *mut leanh::LeanObject,
    mut v___y_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l_reduceCtorEq___lam__1(
        v_x_1917_,
        v_x_1918_,
        v___y_1919_,
        v___y_1920_,
        v___y_1921_,
        v___y_1922_,
        v___y_1923_,
        v___y_1924_,
        v___y_1925_,
    );
    leanh::lean_dec(v___y_1925_);
    leanh::lean_dec_ref(v___y_1924_);
    leanh::lean_dec(v___y_1923_);
    leanh::lean_dec_ref(v___y_1922_);
    leanh::lean_dec(v___y_1921_);
    leanh::lean_dec_ref(v___y_1920_);
    leanh::lean_dec(v___y_1919_);
    leanh::lean_dec(v_x_1918_);
    leanh::lean_dec(v_x_1917_);
    return v_res_1927_;
}
pub unsafe fn _init_l_reduceCtorEq___lam__2___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = leanh::lean_box(0);
    v___x_1932_ = l_reduceCtorEq___lam__2___closed__1;
    v___x_1933_ = l_Lean_mkConst(v___x_1932_, v___x_1931_);
    return v___x_1933_;
}
pub unsafe fn _init_l_reduceCtorEq___lam__2___closed__3() -> u64 {
    let mut v___x_1934_: u8 = 0;
    let mut v___x_1935_: u64 = 0;
    v___x_1934_ = 1;
    v___x_1935_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1934_);
    return v___x_1935_;
}
pub unsafe fn l_reduceCtorEq___lam__2(
    mut v___x_1936_: u8,
    mut v___x_1937_: u8,
    mut v___x_1938_: u64,
    mut v_h_1939_: *mut leanh::LeanObject,
    mut v___y_1940_: *mut leanh::LeanObject,
    mut v___y_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
    mut v___y_1943_: *mut leanh::LeanObject,
    mut v___y_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1964_: u8 = 0;
    let mut v_ctxApprox_1965_: u8 = 0;
    let mut v_quasiPatternApprox_1966_: u8 = 0;
    let mut v_constApprox_1967_: u8 = 0;
    let mut v_isDefEqStuckEx_1968_: u8 = 0;
    let mut v_unificationHints_1969_: u8 = 0;
    let mut v_proofIrrelevance_1970_: u8 = 0;
    let mut v_assignSyntheticOpaque_1971_: u8 = 0;
    let mut v_offsetCnstrs_1972_: u8 = 0;
    let mut v_etaStruct_1973_: u8 = 0;
    let mut v_univApprox_1974_: u8 = 0;
    let mut v_iota_1975_: u8 = 0;
    let mut v_beta_1976_: u8 = 0;
    let mut v_proj_1977_: u8 = 0;
    let mut v_zeta_1978_: u8 = 0;
    let mut v_zetaDelta_1979_: u8 = 0;
    let mut v_zetaUnused_1980_: u8 = 0;
    let mut v_zetaHave_1981_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v_trackZetaDelta_1985_: u8 = 0;
    let mut v_zetaDeltaSet_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1992_: u8 = 0;
    let mut v_inTypeClassResolution_1993_: u8 = 0;
    let mut v_cacheInferType_1994_: u8 = 0;
    let mut v___x_1995_: u8 = 0;
    let mut v_config_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: u64 = 0;
    let mut v___x_1999_: u64 = 0;
    let mut v___x_2000_: u64 = 0;
    let mut v___x_2001_: u64 = 0;
    let mut v_key_2002_: u64 = 0;
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_reuseFailAlloc_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_a_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_a_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1948_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__2),
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__2_once),
                    _init_l_reduceCtorEq___lam__2___closed__2,
                );
                leanh::lean_inc_ref(v_h_1939_);
                v___x_1955_ = l_Lean_Meta_mkNoConfusion(
                    v___x_1948_,
                    v_h_1939_,
                    v___y_1943_,
                    v___y_1944_,
                    v___y_1945_,
                    v___y_1946_,
                );
                if leanh::lean_obj_tag(v___x_1955_) == 0 {
                    v_a_1956_ = leanh::lean_ctor_get(v___x_1955_, 0);
                    leanh::lean_inc(v_a_1956_);
                    leanh::lean_dec_ref_known(v___x_1955_, 1);
                    v___x_1957_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1958_ = lean_mk_empty_array_with_capacity(v___x_1957_);
                    v___x_1959_ = lean_array_push(v___x_1958_, v_h_1939_);
                    v___x_1960_ = 1;
                    v___x_1961_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_1959_,
                        v_a_1956_,
                        v___x_1936_,
                        v___x_1937_,
                        v___x_1936_,
                        v___x_1937_,
                        v___x_1960_,
                        v___y_1943_,
                        v___y_1944_,
                        v___y_1945_,
                        v___y_1946_,
                    );
                    leanh::lean_dec_ref(v___x_1959_);
                    if leanh::lean_obj_tag(v___x_1961_) == 0 {
                        v_a_1962_ = leanh::lean_ctor_get(v___x_1961_, 0);
                        leanh::lean_inc(v_a_1962_);
                        leanh::lean_dec_ref_known(v___x_1961_, 1);
                        v___x_1963_ = l_Lean_Meta_Context_config(v___y_1943_);
                        v_foApprox_1964_ = leanh::lean_ctor_get_uint8(v___x_1963_, 0 as u32);
                        v_ctxApprox_1965_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 1 as u32);
                        v_quasiPatternApprox_1966_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 2 as u32);
                        v_constApprox_1967_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 3 as u32);
                        v_isDefEqStuckEx_1968_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 4 as u32);
                        v_unificationHints_1969_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 5 as u32);
                        v_proofIrrelevance_1970_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 6 as u32);
                        v_assignSyntheticOpaque_1971_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 7 as u32);
                        v_offsetCnstrs_1972_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 8 as u32);
                        v_etaStruct_1973_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 10 as u32);
                        v_univApprox_1974_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 11 as u32);
                        v_iota_1975_ = leanh::lean_ctor_get_uint8(v___x_1963_, 12 as u32);
                        v_beta_1976_ = leanh::lean_ctor_get_uint8(v___x_1963_, 13 as u32);
                        v_proj_1977_ = leanh::lean_ctor_get_uint8(v___x_1963_, 14 as u32);
                        v_zeta_1978_ = leanh::lean_ctor_get_uint8(v___x_1963_, 15 as u32);
                        v_zetaDelta_1979_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 16 as u32);
                        v_zetaUnused_1980_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 17 as u32);
                        v_zetaHave_1981_ =
                            leanh::lean_ctor_get_uint8(v___x_1963_, 18 as u32);
                        v_isSharedCheck_2017_ =
                            (!leanh::lean_is_exclusive(v___x_1963_)) as u8;
                        if v_isSharedCheck_2017_ == 0 {
                            v___x_1983_ = v___x_1963_;
                            v_isShared_1984_ = v_isSharedCheck_2017_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1963_);
                            v___x_1983_ = leanh::lean_box(0);
                            v_isShared_1984_ = v_isSharedCheck_2017_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2018_ = leanh::lean_ctor_get(v___x_1961_, 0);
                        v_isSharedCheck_2025_ =
                            (!leanh::lean_is_exclusive(v___x_1961_)) as u8;
                        if v_isSharedCheck_2025_ == 0 {
                            v___x_2020_ = v___x_1961_;
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2018_);
                            leanh::lean_dec(v___x_1961_);
                            v___x_2020_ = leanh::lean_box(0);
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_h_1939_);
                    v_a_2026_ = leanh::lean_ctor_get(v___x_1955_, 0);
                    v_isSharedCheck_2033_ = (!leanh::lean_is_exclusive(v___x_1955_)) as u8;
                    if v_isSharedCheck_2033_ == 0 {
                        v___x_2028_ = v___x_1955_;
                        v_isShared_2029_ = v_isSharedCheck_2033_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2026_);
                        leanh::lean_dec(v___x_1955_);
                        v___x_2028_ = leanh::lean_box(0);
                        v_isShared_2029_ = v_isSharedCheck_2033_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1951_, 0, v_a_1950_);
                v___x_1952_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1952_, 0, v___x_1948_);
                leanh::lean_ctor_set(v___x_1952_, 1, v___x_1951_);
                leanh::lean_ctor_set_uint8(
                    v___x_1952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1937_,
                );
                v___x_1953_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1953_, 0, v___x_1952_);
                v___x_1954_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                return v___x_1954_;
            }
            2 => {
                v_trackZetaDelta_1985_ = leanh::lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1986_ = leanh::lean_ctor_get(v___y_1943_, 1);
                v_lctx_1987_ = leanh::lean_ctor_get(v___y_1943_, 2);
                v_localInstances_1988_ = leanh::lean_ctor_get(v___y_1943_, 3);
                v_defEqCtx_x3f_1989_ = leanh::lean_ctor_get(v___y_1943_, 4);
                v_synthPendingDepth_1990_ = leanh::lean_ctor_get(v___y_1943_, 5);
                v_canUnfold_x3f_1991_ = leanh::lean_ctor_get(v___y_1943_, 6);
                v_univApprox_1992_ = leanh::lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1993_ = leanh::lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1994_ = leanh::lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1995_ = 1;
                if v_isShared_1984_ == 0 {
                    v_config_1997_ = v___x_1983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        0 as u32,
                        v_foApprox_1964_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        1 as u32,
                        v_ctxApprox_1965_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        2 as u32,
                        v_quasiPatternApprox_1966_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        3 as u32,
                        v_constApprox_1967_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        4 as u32,
                        v_isDefEqStuckEx_1968_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        5 as u32,
                        v_unificationHints_1969_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        6 as u32,
                        v_proofIrrelevance_1970_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        7 as u32,
                        v_assignSyntheticOpaque_1971_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        8 as u32,
                        v_offsetCnstrs_1972_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        10 as u32,
                        v_etaStruct_1973_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        11 as u32,
                        v_univApprox_1974_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        12 as u32,
                        v_iota_1975_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        13 as u32,
                        v_beta_1976_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        14 as u32,
                        v_proj_1977_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        15 as u32,
                        v_zeta_1978_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        16 as u32,
                        v_zetaDelta_1979_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        17 as u32,
                        v_zetaUnused_1980_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        18 as u32,
                        v_zetaHave_1981_,
                    );
                    v_config_1997_ = v_reuseFailAlloc_2016_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(v_config_1997_, 9 as u32, v___x_1995_);
                v___x_1998_ = l_Lean_Meta_Context_configKey(v___y_1943_);
                v___x_1999_ = lean_uint64_shift_right(v___x_1998_, v___x_1938_);
                v___x_2000_ = lean_uint64_shift_left(v___x_1999_, v___x_1938_);
                v___x_2001_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__3),
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__3_once),
                    _init_l_reduceCtorEq___lam__2___closed__3,
                );
                v_key_2002_ = lean_uint64_lor(v___x_2000_, v___x_2001_);
                v___x_2003_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2003_, 0, v_config_1997_);
                leanh::lean_ctor_set_uint64(
                    v___x_2003_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2002_,
                );
                leanh::lean_inc(v_canUnfold_x3f_1991_);
                leanh::lean_inc(v_synthPendingDepth_1990_);
                leanh::lean_inc(v_defEqCtx_x3f_1989_);
                leanh::lean_inc_ref(v_localInstances_1988_);
                leanh::lean_inc_ref(v_lctx_1987_);
                leanh::lean_inc(v_zetaDeltaSet_1986_);
                v___x_2004_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2004_, 0, v___x_2003_);
                leanh::lean_ctor_set(v___x_2004_, 1, v_zetaDeltaSet_1986_);
                leanh::lean_ctor_set(v___x_2004_, 2, v_lctx_1987_);
                leanh::lean_ctor_set(v___x_2004_, 3, v_localInstances_1988_);
                leanh::lean_ctor_set(v___x_2004_, 4, v_defEqCtx_x3f_1989_);
                leanh::lean_ctor_set(v___x_2004_, 5, v_synthPendingDepth_1990_);
                leanh::lean_ctor_set(v___x_2004_, 6, v_canUnfold_x3f_1991_);
                leanh::lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1985_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1992_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1993_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1994_,
                );
                v___x_2005_ = l_Lean_Meta_mkEqFalse_x27(
                    v_a_1962_,
                    v___x_2004_,
                    v___y_1944_,
                    v___y_1945_,
                    v___y_1946_,
                );
                leanh::lean_dec_ref_known(v___x_2004_, 7);
                if leanh::lean_obj_tag(v___x_2005_) == 0 {
                    v_a_2006_ = leanh::lean_ctor_get(v___x_2005_, 0);
                    leanh::lean_inc(v_a_2006_);
                    leanh::lean_dec_ref_known(v___x_2005_, 1);
                    v_a_1950_ = v_a_2006_;
                    state = 1;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_2005_) == 0 {
                        v_a_2007_ = leanh::lean_ctor_get(v___x_2005_, 0);
                        leanh::lean_inc(v_a_2007_);
                        leanh::lean_dec_ref_known(v___x_2005_, 1);
                        v_a_1950_ = v_a_2007_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2008_ = leanh::lean_ctor_get(v___x_2005_, 0);
                        v_isSharedCheck_2015_ =
                            (!leanh::lean_is_exclusive(v___x_2005_)) as u8;
                        if v_isSharedCheck_2015_ == 0 {
                            v___x_2010_ = v___x_2005_;
                            v_isShared_2011_ = v_isSharedCheck_2015_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2008_);
                            leanh::lean_dec(v___x_2005_);
                            v___x_2010_ = leanh::lean_box(0);
                            v_isShared_2011_ = v_isSharedCheck_2015_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_2011_ == 0 {
                    v___x_2013_ = v___x_2010_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2013_;
            }
            6 => {
                if v_isShared_2021_ == 0 {
                    v___x_2023_ = v___x_2020_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2023_;
            }
            8 => {
                if v_isShared_2029_ == 0 {
                    v___x_2031_ = v___x_2028_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
                    v___x_2031_ = v_reuseFailAlloc_2032_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_reduceCtorEq___lam__2___boxed(
    mut v___x_2034_: *mut leanh::LeanObject,
    mut v___x_2035_: *mut leanh::LeanObject,
    mut v___x_2036_: *mut leanh::LeanObject,
    mut v_h_2037_: *mut leanh::LeanObject,
    mut v___y_2038_: *mut leanh::LeanObject,
    mut v___y_2039_: *mut leanh::LeanObject,
    mut v___y_2040_: *mut leanh::LeanObject,
    mut v___y_2041_: *mut leanh::LeanObject,
    mut v___y_2042_: *mut leanh::LeanObject,
    mut v___y_2043_: *mut leanh::LeanObject,
    mut v___y_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_26663__boxed_2046_: u8 = 0;
    let mut v___x_26664__boxed_2047_: u8 = 0;
    let mut v___x_26665__boxed_2048_: u64 = 0;
    let mut v_res_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_26663__boxed_2046_ = (leanh::lean_unbox(v___x_2034_) as u8);
    v___x_26664__boxed_2047_ = (leanh::lean_unbox(v___x_2035_) as u8);
    v___x_26665__boxed_2048_ = leanh::lean_unbox_uint64(v___x_2036_);
    leanh::lean_dec_ref(v___x_2036_);
    v_res_2049_ = l_reduceCtorEq___lam__2(
        v___x_26663__boxed_2046_,
        v___x_26664__boxed_2047_,
        v___x_26665__boxed_2048_,
        v_h_2037_,
        v___y_2038_,
        v___y_2039_,
        v___y_2040_,
        v___y_2041_,
        v___y_2042_,
        v___y_2043_,
        v___y_2044_,
    );
    leanh::lean_dec(v___y_2044_);
    leanh::lean_dec_ref(v___y_2043_);
    leanh::lean_dec(v___y_2042_);
    leanh::lean_dec_ref(v___y_2041_);
    leanh::lean_dec(v___y_2040_);
    leanh::lean_dec_ref(v___y_2039_);
    leanh::lean_dec(v___y_2038_);
    return v_res_2049_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(
    mut v_k_2050_: *mut leanh::LeanObject,
    mut v___y_2051_: *mut leanh::LeanObject,
    mut v___y_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v_b_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2058_);
    leanh::lean_inc_ref(v___y_2057_);
    leanh::lean_inc(v___y_2056_);
    leanh::lean_inc_ref(v___y_2055_);
    leanh::lean_inc(v___y_2053_);
    leanh::lean_inc_ref(v___y_2052_);
    leanh::lean_inc(v___y_2051_);
    v___x_2060_ = leanh::lean_apply_9(
        v_k_2050_,
        v_b_2054_,
        v___y_2051_,
        v___y_2052_,
        v___y_2053_,
        v___y_2055_,
        v___y_2056_,
        v___y_2057_,
        v___y_2058_,
        leanh::lean_box(0),
    );
    return v___x_2060_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
    mut v_b_2065_: *mut leanh::LeanObject,
    mut v___y_2066_: *mut leanh::LeanObject,
    mut v___y_2067_: *mut leanh::LeanObject,
    mut v___y_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2071_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v_b_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
    leanh::lean_dec(v___y_2069_);
    leanh::lean_dec_ref(v___y_2068_);
    leanh::lean_dec(v___y_2067_);
    leanh::lean_dec_ref(v___y_2066_);
    leanh::lean_dec(v___y_2064_);
    leanh::lean_dec_ref(v___y_2063_);
    leanh::lean_dec(v___y_2062_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(
    mut v_name_2072_: *mut leanh::LeanObject,
    mut v_bi_2073_: u8,
    mut v_type_2074_: *mut leanh::LeanObject,
    mut v_k_2075_: *mut leanh::LeanObject,
    mut v_kind_2076_: u8,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
    mut v___y_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2079_);
                leanh::lean_inc_ref(v___y_2078_);
                leanh::lean_inc(v___y_2077_);
                v___f_2085_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                leanh::lean_closure_set(v___f_2085_, 0, v_k_2075_);
                leanh::lean_closure_set(v___f_2085_, 1, v___y_2077_);
                leanh::lean_closure_set(v___f_2085_, 2, v___y_2078_);
                leanh::lean_closure_set(v___f_2085_, 3, v___y_2079_);
                v___x_2086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_2072_,
                    v_bi_2073_,
                    v_type_2074_,
                    v___f_2085_,
                    v_kind_2076_,
                    v___y_2080_,
                    v___y_2081_,
                    v___y_2082_,
                    v___y_2083_,
                );
                if leanh::lean_obj_tag(v___x_2086_) == 0 {
                    return v___x_2086_;
                } else {
                    v_a_2087_ = leanh::lean_ctor_get(v___x_2086_, 0);
                    v_isSharedCheck_2094_ = (!leanh::lean_is_exclusive(v___x_2086_)) as u8;
                    if v_isSharedCheck_2094_ == 0 {
                        v___x_2089_ = v___x_2086_;
                        v_isShared_2090_ = v_isSharedCheck_2094_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2087_);
                        leanh::lean_dec(v___x_2086_);
                        v___x_2089_ = leanh::lean_box(0);
                        v_isShared_2090_ = v_isSharedCheck_2094_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2090_ == 0 {
                    v___x_2092_ = v___x_2089_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
                    v___x_2092_ = v_reuseFailAlloc_2093_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___boxed(
    mut v_name_2095_: *mut leanh::LeanObject,
    mut v_bi_2096_: *mut leanh::LeanObject,
    mut v_type_2097_: *mut leanh::LeanObject,
    mut v_k_2098_: *mut leanh::LeanObject,
    mut v_kind_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
    mut v___y_2101_: *mut leanh::LeanObject,
    mut v___y_2102_: *mut leanh::LeanObject,
    mut v___y_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
    mut v___y_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_2108_: u8 = 0;
    let mut v_kind_boxed_2109_: u8 = 0;
    let mut v_res_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2108_ = (leanh::lean_unbox(v_bi_2096_) as u8);
    v_kind_boxed_2109_ = (leanh::lean_unbox(v_kind_2099_) as u8);
    v_res_2110_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_2095_, v_bi_boxed_2108_, v_type_2097_, v_k_2098_, v_kind_boxed_2109_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
    leanh::lean_dec(v___y_2106_);
    leanh::lean_dec_ref(v___y_2105_);
    leanh::lean_dec(v___y_2104_);
    leanh::lean_dec_ref(v___y_2103_);
    leanh::lean_dec(v___y_2102_);
    leanh::lean_dec_ref(v___y_2101_);
    leanh::lean_dec(v___y_2100_);
    return v_res_2110_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(
    mut v_name_2111_: *mut leanh::LeanObject,
    mut v_type_2112_: *mut leanh::LeanObject,
    mut v_k_2113_: *mut leanh::LeanObject,
    mut v___y_2114_: *mut leanh::LeanObject,
    mut v___y_2115_: *mut leanh::LeanObject,
    mut v___y_2116_: *mut leanh::LeanObject,
    mut v___y_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: u8 = 0;
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = 0;
    v___x_2123_ = 0;
    v___x_2124_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_2111_, v___x_2122_, v_type_2112_, v_k_2113_, v___x_2123_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
    return v___x_2124_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(
    mut v_name_2125_: *mut leanh::LeanObject,
    mut v_type_2126_: *mut leanh::LeanObject,
    mut v_k_2127_: *mut leanh::LeanObject,
    mut v___y_2128_: *mut leanh::LeanObject,
    mut v___y_2129_: *mut leanh::LeanObject,
    mut v___y_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
    mut v___y_2132_: *mut leanh::LeanObject,
    mut v___y_2133_: *mut leanh::LeanObject,
    mut v___y_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2136_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(
        v_name_2125_,
        v_type_2126_,
        v_k_2127_,
        v___y_2128_,
        v___y_2129_,
        v___y_2130_,
        v___y_2131_,
        v___y_2132_,
        v___y_2133_,
        v___y_2134_,
    );
    leanh::lean_dec(v___y_2134_);
    leanh::lean_dec_ref(v___y_2133_);
    leanh::lean_dec(v___y_2132_);
    leanh::lean_dec_ref(v___y_2131_);
    leanh::lean_dec(v___y_2130_);
    leanh::lean_dec_ref(v___y_2129_);
    leanh::lean_dec(v___y_2128_);
    return v_res_2136_;
}
pub unsafe fn _init_l_reduceCtorEq___closed__0() -> u64 {
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2138_: u64 = 0;
    v___x_2137_ = 3;
    v___x_2138_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2137_);
    return v___x_2138_;
}
pub unsafe fn l_reduceCtorEq(
    mut v_e_2147_: *mut leanh::LeanObject,
    mut v_a_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
    mut v_a_2152_: *mut leanh::LeanObject,
    mut v_a_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2167_: u8 = 0;
    let mut v_ctxApprox_2168_: u8 = 0;
    let mut v_quasiPatternApprox_2169_: u8 = 0;
    let mut v_constApprox_2170_: u8 = 0;
    let mut v_isDefEqStuckEx_2171_: u8 = 0;
    let mut v_unificationHints_2172_: u8 = 0;
    let mut v_proofIrrelevance_2173_: u8 = 0;
    let mut v_assignSyntheticOpaque_2174_: u8 = 0;
    let mut v_offsetCnstrs_2175_: u8 = 0;
    let mut v_etaStruct_2176_: u8 = 0;
    let mut v_univApprox_2177_: u8 = 0;
    let mut v_iota_2178_: u8 = 0;
    let mut v_beta_2179_: u8 = 0;
    let mut v_proj_2180_: u8 = 0;
    let mut v_zeta_2181_: u8 = 0;
    let mut v_zetaDelta_2182_: u8 = 0;
    let mut v_zetaUnused_2183_: u8 = 0;
    let mut v_zetaHave_2184_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v_trackZetaDelta_2188_: u8 = 0;
    let mut v_zetaDeltaSet_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2195_: u8 = 0;
    let mut v_inTypeClassResolution_2196_: u8 = 0;
    let mut v_cacheInferType_2197_: u8 = 0;
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v_config_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u64 = 0;
    let mut v___x_2204_: u64 = 0;
    let mut v___x_2205_: u64 = 0;
    let mut v___x_2206_: u64 = 0;
    let mut v___x_2207_: u64 = 0;
    let mut v_key_2208_: u64 = 0;
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v_a_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2263_: u8 = 0;
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2267_: u8 = 0;
    let mut v_a_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_reuseFailAlloc_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2166_ = l_Lean_Meta_Context_config(v_a_2151_);
                v_foApprox_2167_ = leanh::lean_ctor_get_uint8(v___x_2166_, 0 as u32);
                v_ctxApprox_2168_ = leanh::lean_ctor_get_uint8(v___x_2166_, 1 as u32);
                v_quasiPatternApprox_2169_ =
                    leanh::lean_ctor_get_uint8(v___x_2166_, 2 as u32);
                v_constApprox_2170_ = leanh::lean_ctor_get_uint8(v___x_2166_, 3 as u32);
                v_isDefEqStuckEx_2171_ = leanh::lean_ctor_get_uint8(v___x_2166_, 4 as u32);
                v_unificationHints_2172_ = leanh::lean_ctor_get_uint8(v___x_2166_, 5 as u32);
                v_proofIrrelevance_2173_ = leanh::lean_ctor_get_uint8(v___x_2166_, 6 as u32);
                v_assignSyntheticOpaque_2174_ =
                    leanh::lean_ctor_get_uint8(v___x_2166_, 7 as u32);
                v_offsetCnstrs_2175_ = leanh::lean_ctor_get_uint8(v___x_2166_, 8 as u32);
                v_etaStruct_2176_ = leanh::lean_ctor_get_uint8(v___x_2166_, 10 as u32);
                v_univApprox_2177_ = leanh::lean_ctor_get_uint8(v___x_2166_, 11 as u32);
                v_iota_2178_ = leanh::lean_ctor_get_uint8(v___x_2166_, 12 as u32);
                v_beta_2179_ = leanh::lean_ctor_get_uint8(v___x_2166_, 13 as u32);
                v_proj_2180_ = leanh::lean_ctor_get_uint8(v___x_2166_, 14 as u32);
                v_zeta_2181_ = leanh::lean_ctor_get_uint8(v___x_2166_, 15 as u32);
                v_zetaDelta_2182_ = leanh::lean_ctor_get_uint8(v___x_2166_, 16 as u32);
                v_zetaUnused_2183_ = leanh::lean_ctor_get_uint8(v___x_2166_, 17 as u32);
                v_zetaHave_2184_ = leanh::lean_ctor_get_uint8(v___x_2166_, 18 as u32);
                v_isSharedCheck_2285_ = (!leanh::lean_is_exclusive(v___x_2166_)) as u8;
                if v_isSharedCheck_2285_ == 0 {
                    v___x_2186_ = v___x_2166_;
                    v_isShared_2187_ = v_isSharedCheck_2285_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2166_);
                    v___x_2186_ = leanh::lean_box(0);
                    v_isShared_2187_ = v_isSharedCheck_2285_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2157_) == 0 {
                    v_a_2158_ = leanh::lean_ctor_get(v___y_2157_, 0);
                    v_isSharedCheck_2165_ = (!leanh::lean_is_exclusive(v___y_2157_)) as u8;
                    if v_isSharedCheck_2165_ == 0 {
                        v___x_2160_ = v___y_2157_;
                        v_isShared_2161_ = v_isSharedCheck_2165_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2158_);
                        leanh::lean_dec(v___y_2157_);
                        v___x_2160_ = leanh::lean_box(0);
                        v_isShared_2161_ = v_isSharedCheck_2165_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_2157_;
                }
            }
            2 => {
                if v_isShared_2161_ == 0 {
                    v___x_2163_ = v___x_2160_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
                    v___x_2163_ = v_reuseFailAlloc_2164_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2163_;
            }
            4 => {
                v_trackZetaDelta_2188_ = leanh::lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2189_ = leanh::lean_ctor_get(v_a_2151_, 1);
                v_lctx_2190_ = leanh::lean_ctor_get(v_a_2151_, 2);
                v_localInstances_2191_ = leanh::lean_ctor_get(v_a_2151_, 3);
                v_defEqCtx_x3f_2192_ = leanh::lean_ctor_get(v_a_2151_, 4);
                v_synthPendingDepth_2193_ = leanh::lean_ctor_get(v_a_2151_, 5);
                v_canUnfold_x3f_2194_ = leanh::lean_ctor_get(v_a_2151_, 6);
                v_univApprox_2195_ = leanh::lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2196_ = leanh::lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2197_ = leanh::lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                leanh::lean_inc_ref(v_e_2147_);
                v___x_2198_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2147_, v_a_2152_);
                if leanh::lean_obj_tag(v___x_2198_) == 0 {
                    v_a_2199_ = leanh::lean_ctor_get(v___x_2198_, 0);
                    leanh::lean_inc(v_a_2199_);
                    leanh::lean_dec_ref_known(v___x_2198_, 1);
                    v___x_2200_ = 3;
                    if v_isShared_2187_ == 0 {
                        v_config_2202_ = v___x_2186_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2276_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            0 as u32,
                            v_foApprox_2167_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            1 as u32,
                            v_ctxApprox_2168_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            2 as u32,
                            v_quasiPatternApprox_2169_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            3 as u32,
                            v_constApprox_2170_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            4 as u32,
                            v_isDefEqStuckEx_2171_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            5 as u32,
                            v_unificationHints_2172_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            6 as u32,
                            v_proofIrrelevance_2173_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            7 as u32,
                            v_assignSyntheticOpaque_2174_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            8 as u32,
                            v_offsetCnstrs_2175_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            10 as u32,
                            v_etaStruct_2176_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            11 as u32,
                            v_univApprox_2177_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            12 as u32,
                            v_iota_2178_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            13 as u32,
                            v_beta_2179_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            14 as u32,
                            v_proj_2180_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            15 as u32,
                            v_zeta_2181_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            16 as u32,
                            v_zetaDelta_2182_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            17 as u32,
                            v_zetaUnused_2183_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            18 as u32,
                            v_zetaHave_2184_,
                        );
                        v_config_2202_ = v_reuseFailAlloc_2276_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2186_);
                    leanh::lean_dec_ref(v_e_2147_);
                    v_a_2277_ = leanh::lean_ctor_get(v___x_2198_, 0);
                    v_isSharedCheck_2284_ = (!leanh::lean_is_exclusive(v___x_2198_)) as u8;
                    if v_isSharedCheck_2284_ == 0 {
                        v___x_2279_ = v___x_2198_;
                        v_isShared_2280_ = v_isSharedCheck_2284_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2277_);
                        leanh::lean_dec(v___x_2198_);
                        v___x_2279_ = leanh::lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2284_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(v_config_2202_, 9 as u32, v___x_2200_);
                v___x_2203_ = l_Lean_Meta_Context_configKey(v_a_2151_);
                v___x_2204_ = 3u64;
                v___x_2205_ = lean_uint64_shift_right(v___x_2203_, v___x_2204_);
                v___x_2206_ = lean_uint64_shift_left(v___x_2205_, v___x_2204_);
                v___x_2207_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_reduceCtorEq___closed__0),
                    core::ptr::addr_of_mut!(l_reduceCtorEq___closed__0_once),
                    _init_l_reduceCtorEq___closed__0,
                );
                v_key_2208_ = lean_uint64_lor(v___x_2206_, v___x_2207_);
                v___x_2209_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2209_, 0, v_config_2202_);
                leanh::lean_ctor_set_uint64(
                    v___x_2209_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2208_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2194_);
                leanh::lean_inc(v_synthPendingDepth_2193_);
                leanh::lean_inc(v_defEqCtx_x3f_2192_);
                leanh::lean_inc_ref(v_localInstances_2191_);
                leanh::lean_inc_ref(v_lctx_2190_);
                leanh::lean_inc(v_zetaDeltaSet_2189_);
                v___x_2210_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
                leanh::lean_ctor_set(v___x_2210_, 1, v_zetaDeltaSet_2189_);
                leanh::lean_ctor_set(v___x_2210_, 2, v_lctx_2190_);
                leanh::lean_ctor_set(v___x_2210_, 3, v_localInstances_2191_);
                leanh::lean_ctor_set(v___x_2210_, 4, v_defEqCtx_x3f_2192_);
                leanh::lean_ctor_set(v___x_2210_, 5, v_synthPendingDepth_2193_);
                leanh::lean_ctor_set(v___x_2210_, 6, v_canUnfold_x3f_2194_);
                leanh::lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2188_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2195_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2196_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2197_,
                );
                v___x_2211_ = l_Lean_Expr_cleanupAnnotations(v_a_2199_);
                v___x_2212_ = l_Lean_Expr_isApp(v___x_2211_);
                if v___x_2212_ == 0 {
                    leanh::lean_dec_ref(v___x_2211_);
                    leanh::lean_dec_ref(v_e_2147_);
                    v___x_2213_ = leanh::lean_box(0);
                    v___x_2214_ = l_reduceCtorEq___lam__0(
                        v___x_2213_,
                        v_a_2148_,
                        v_a_2149_,
                        v_a_2150_,
                        v___x_2210_,
                        v_a_2152_,
                        v_a_2153_,
                        v_a_2154_,
                    );
                    leanh::lean_dec_ref_known(v___x_2210_, 7);
                    v___y_2157_ = v___x_2214_;
                    state = 1;
                    continue;
                } else {
                    v_arg_2215_ = leanh::lean_ctor_get(v___x_2211_, 1);
                    leanh::lean_inc_ref(v_arg_2215_);
                    v___x_2216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2211_);
                    v___x_2217_ = l_Lean_Expr_isApp(v___x_2216_);
                    if v___x_2217_ == 0 {
                        leanh::lean_dec_ref(v___x_2216_);
                        leanh::lean_dec_ref(v_arg_2215_);
                        leanh::lean_dec_ref(v_e_2147_);
                        v___x_2218_ = leanh::lean_box(0);
                        v___x_2219_ = l_reduceCtorEq___lam__0(
                            v___x_2218_,
                            v_a_2148_,
                            v_a_2149_,
                            v_a_2150_,
                            v___x_2210_,
                            v_a_2152_,
                            v_a_2153_,
                            v_a_2154_,
                        );
                        leanh::lean_dec_ref_known(v___x_2210_, 7);
                        v___y_2157_ = v___x_2219_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_2220_ = leanh::lean_ctor_get(v___x_2216_, 1);
                        leanh::lean_inc_ref(v_arg_2220_);
                        v___x_2221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2216_);
                        v___x_2222_ = l_Lean_Expr_isApp(v___x_2221_);
                        if v___x_2222_ == 0 {
                            leanh::lean_dec_ref(v___x_2221_);
                            leanh::lean_dec_ref(v_arg_2220_);
                            leanh::lean_dec_ref(v_arg_2215_);
                            leanh::lean_dec_ref(v_e_2147_);
                            v___x_2223_ = leanh::lean_box(0);
                            v___x_2224_ = l_reduceCtorEq___lam__0(
                                v___x_2223_,
                                v_a_2148_,
                                v_a_2149_,
                                v_a_2150_,
                                v___x_2210_,
                                v_a_2152_,
                                v_a_2153_,
                                v_a_2154_,
                            );
                            leanh::lean_dec_ref_known(v___x_2210_, 7);
                            v___y_2157_ = v___x_2224_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2221_);
                            v___x_2226_ = l_reduceCtorEq___closed__2;
                            v___x_2227_ = l_Lean_Expr_isConstOf(v___x_2225_, v___x_2226_);
                            leanh::lean_dec_ref(v___x_2225_);
                            if v___x_2227_ == 0 {
                                leanh::lean_dec_ref(v_arg_2220_);
                                leanh::lean_dec_ref(v_arg_2215_);
                                leanh::lean_dec_ref(v_e_2147_);
                                v___x_2228_ = leanh::lean_box(0);
                                v___x_2229_ = l_reduceCtorEq___lam__0(
                                    v___x_2228_,
                                    v_a_2148_,
                                    v_a_2149_,
                                    v_a_2150_,
                                    v___x_2210_,
                                    v_a_2152_,
                                    v_a_2153_,
                                    v_a_2154_,
                                );
                                leanh::lean_dec_ref_known(v___x_2210_, 7);
                                v___y_2157_ = v___x_2229_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2230_ = l_Lean_Meta_constructorApp_x27_x3f(
                                    v_arg_2220_,
                                    v___x_2210_,
                                    v_a_2152_,
                                    v_a_2153_,
                                    v_a_2154_,
                                );
                                if leanh::lean_obj_tag(v___x_2230_) == 0 {
                                    v_a_2231_ = leanh::lean_ctor_get(v___x_2230_, 0);
                                    leanh::lean_inc(v_a_2231_);
                                    leanh::lean_dec_ref_known(v___x_2230_, 1);
                                    v___x_2232_ = l_Lean_Meta_constructorApp_x27_x3f(
                                        v_arg_2215_,
                                        v___x_2210_,
                                        v_a_2152_,
                                        v_a_2153_,
                                        v_a_2154_,
                                    );
                                    if leanh::lean_obj_tag(v___x_2232_) == 0 {
                                        v_a_2233_ = leanh::lean_ctor_get(v___x_2232_, 0);
                                        v_isSharedCheck_2259_ =
                                            (!leanh::lean_is_exclusive(v___x_2232_)) as u8;
                                        if v_isSharedCheck_2259_ == 0 {
                                            v___x_2235_ = v___x_2232_;
                                            v_isShared_2236_ = v_isSharedCheck_2259_;
                                            state = 6;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2233_);
                                            leanh::lean_dec(v___x_2232_);
                                            v___x_2235_ = leanh::lean_box(0);
                                            v_isShared_2236_ = v_isSharedCheck_2259_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_2231_);
                                        leanh::lean_dec_ref_known(v___x_2210_, 7);
                                        leanh::lean_dec_ref(v_e_2147_);
                                        v_a_2260_ = leanh::lean_ctor_get(v___x_2232_, 0);
                                        v_isSharedCheck_2267_ =
                                            (!leanh::lean_is_exclusive(v___x_2232_)) as u8;
                                        if v_isSharedCheck_2267_ == 0 {
                                            v___x_2262_ = v___x_2232_;
                                            v_isShared_2263_ = v_isSharedCheck_2267_;
                                            state = 9;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2260_);
                                            leanh::lean_dec(v___x_2232_);
                                            v___x_2262_ = leanh::lean_box(0);
                                            v_isShared_2263_ = v_isSharedCheck_2267_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_2215_);
                                    leanh::lean_dec_ref_known(v___x_2210_, 7);
                                    leanh::lean_dec_ref(v_e_2147_);
                                    v_a_2268_ = leanh::lean_ctor_get(v___x_2230_, 0);
                                    v_isSharedCheck_2275_ =
                                        (!leanh::lean_is_exclusive(v___x_2230_)) as u8;
                                    if v_isSharedCheck_2275_ == 0 {
                                        v___x_2270_ = v___x_2230_;
                                        v_isShared_2271_ = v_isSharedCheck_2275_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2268_);
                                        leanh::lean_dec(v___x_2230_);
                                        v___x_2270_ = leanh::lean_box(0);
                                        v_isShared_2271_ = v_isSharedCheck_2275_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_a_2231_) == 1 {
                    if leanh::lean_obj_tag(v_a_2233_) == 1 {
                        v_val_2242_ = leanh::lean_ctor_get(v_a_2231_, 0);
                        leanh::lean_inc(v_val_2242_);
                        leanh::lean_dec_ref_known(v_a_2231_, 1);
                        v_val_2243_ = leanh::lean_ctor_get(v_a_2233_, 0);
                        leanh::lean_inc(v_val_2243_);
                        leanh::lean_dec_ref_known(v_a_2233_, 1);
                        v_fst_2244_ = leanh::lean_ctor_get(v_val_2242_, 0);
                        leanh::lean_inc(v_fst_2244_);
                        leanh::lean_dec(v_val_2242_);
                        v_toConstantVal_2245_ = leanh::lean_ctor_get(v_fst_2244_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_2245_);
                        leanh::lean_dec(v_fst_2244_);
                        v_fst_2246_ = leanh::lean_ctor_get(v_val_2243_, 0);
                        leanh::lean_inc(v_fst_2246_);
                        leanh::lean_dec(v_val_2243_);
                        v_toConstantVal_2247_ = leanh::lean_ctor_get(v_fst_2246_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_2247_);
                        leanh::lean_dec(v_fst_2246_);
                        v_name_2248_ = leanh::lean_ctor_get(v_toConstantVal_2245_, 0);
                        leanh::lean_inc(v_name_2248_);
                        leanh::lean_dec_ref(v_toConstantVal_2245_);
                        v_name_2249_ = leanh::lean_ctor_get(v_toConstantVal_2247_, 0);
                        leanh::lean_inc(v_name_2249_);
                        leanh::lean_dec_ref(v_toConstantVal_2247_);
                        v___x_2250_ = lean_name_eq(v_name_2248_, v_name_2249_);
                        leanh::lean_dec(v_name_2249_);
                        leanh::lean_dec(v_name_2248_);
                        if v___x_2250_ == 0 {
                            if v___x_2227_ == 0 {
                                leanh::lean_dec_ref_known(v___x_2210_, 7);
                                leanh::lean_dec_ref(v_e_2147_);
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2235_);
                                v___x_2251_ = leanh::lean_box((v___x_2250_) as usize);
                                v___x_2252_ = leanh::lean_box((v___x_2227_) as usize);
                                v___x_2253_ = l_reduceCtorEq___boxed__const__1;
                                v___f_2254_ = leanh::lean_alloc_closure(
                                    l_reduceCtorEq___lam__2___boxed as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_2254_, 0, v___x_2251_);
                                leanh::lean_closure_set(v___f_2254_, 1, v___x_2252_);
                                leanh::lean_closure_set(v___f_2254_, 2, v___x_2253_);
                                v___x_2255_ = l_reduceCtorEq___closed__4;
                                v___x_2256_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_2255_, v_e_2147_, v___f_2254_, v_a_2148_, v_a_2149_, v_a_2150_, v___x_2210_, v_a_2152_, v_a_2153_, v_a_2154_);
                                leanh::lean_dec_ref_known(v___x_2210_, 7);
                                v___y_2157_ = v___x_2256_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_2210_, 7);
                            leanh::lean_dec_ref(v_e_2147_);
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2235_);
                        leanh::lean_dec_ref(v_e_2147_);
                        v___x_2257_ = l_reduceCtorEq___lam__1(
                            v_a_2231_,
                            v_a_2233_,
                            v_a_2148_,
                            v_a_2149_,
                            v_a_2150_,
                            v___x_2210_,
                            v_a_2152_,
                            v_a_2153_,
                            v_a_2154_,
                        );
                        leanh::lean_dec_ref_known(v___x_2210_, 7);
                        leanh::lean_dec(v_a_2233_);
                        leanh::lean_dec_ref_known(v_a_2231_, 1);
                        v___y_2157_ = v___x_2257_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2235_);
                    leanh::lean_dec_ref(v_e_2147_);
                    v___x_2258_ = l_reduceCtorEq___lam__1(
                        v_a_2231_,
                        v_a_2233_,
                        v_a_2148_,
                        v_a_2149_,
                        v_a_2150_,
                        v___x_2210_,
                        v_a_2152_,
                        v_a_2153_,
                        v_a_2154_,
                    );
                    leanh::lean_dec_ref_known(v___x_2210_, 7);
                    leanh::lean_dec(v_a_2233_);
                    leanh::lean_dec(v_a_2231_);
                    v___y_2157_ = v___x_2258_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_2238_ = l_reduceIte___closed__0;
                if v_isShared_2236_ == 0 {
                    leanh::lean_ctor_set(v___x_2235_, 0, v___x_2238_);
                    v___x_2240_ = v___x_2235_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
                    v___x_2240_ = v_reuseFailAlloc_2241_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2240_;
            }
            9 => {
                if v_isShared_2263_ == 0 {
                    v___x_2265_ = v___x_2262_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
                    v___x_2265_ = v_reuseFailAlloc_2266_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2265_;
            }
            11 => {
                if v_isShared_2271_ == 0 {
                    v___x_2273_ = v___x_2270_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2273_;
            }
            13 => {
                if v_isShared_2280_ == 0 {
                    v___x_2282_ = v___x_2279_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
                    v___x_2282_ = v_reuseFailAlloc_2283_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_reduceCtorEq___boxed(
    mut v_e_2286_: *mut leanh::LeanObject,
    mut v_a_2287_: *mut leanh::LeanObject,
    mut v_a_2288_: *mut leanh::LeanObject,
    mut v_a_2289_: *mut leanh::LeanObject,
    mut v_a_2290_: *mut leanh::LeanObject,
    mut v_a_2291_: *mut leanh::LeanObject,
    mut v_a_2292_: *mut leanh::LeanObject,
    mut v_a_2293_: *mut leanh::LeanObject,
    mut v_a_2294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_reduceCtorEq(
        v_e_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_,
    );
    leanh::lean_dec(v_a_2293_);
    leanh::lean_dec_ref(v_a_2292_);
    leanh::lean_dec(v_a_2291_);
    leanh::lean_dec_ref(v_a_2290_);
    leanh::lean_dec(v_a_2289_);
    leanh::lean_dec_ref(v_a_2288_);
    leanh::lean_dec(v_a_2287_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(
    mut v_00_u03b1_2296_: *mut leanh::LeanObject,
    mut v_name_2297_: *mut leanh::LeanObject,
    mut v_bi_2298_: u8,
    mut v_type_2299_: *mut leanh::LeanObject,
    mut v_k_2300_: *mut leanh::LeanObject,
    mut v_kind_2301_: u8,
    mut v___y_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_2297_, v_bi_2298_, v_type_2299_, v_k_2300_, v_kind_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
    return v___x_2310_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(
    mut v_00_u03b1_2311_: *mut leanh::LeanObject,
    mut v_name_2312_: *mut leanh::LeanObject,
    mut v_bi_2313_: *mut leanh::LeanObject,
    mut v_type_2314_: *mut leanh::LeanObject,
    mut v_k_2315_: *mut leanh::LeanObject,
    mut v_kind_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
    mut v___y_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
    mut v___y_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_2325_: u8 = 0;
    let mut v_kind_boxed_2326_: u8 = 0;
    let mut v_res_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2325_ = (leanh::lean_unbox(v_bi_2313_) as u8);
    v_kind_boxed_2326_ = (leanh::lean_unbox(v_kind_2316_) as u8);
    v_res_2327_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(v_00_u03b1_2311_, v_name_2312_, v_bi_boxed_2325_, v_type_2314_, v_k_2315_, v_kind_boxed_2326_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
    leanh::lean_dec(v___y_2323_);
    leanh::lean_dec_ref(v___y_2322_);
    leanh::lean_dec(v___y_2321_);
    leanh::lean_dec_ref(v___y_2320_);
    leanh::lean_dec(v___y_2319_);
    leanh::lean_dec_ref(v___y_2318_);
    leanh::lean_dec(v___y_2317_);
    return v_res_2327_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(
    mut v_00_u03b1_2328_: *mut leanh::LeanObject,
    mut v_name_2329_: *mut leanh::LeanObject,
    mut v_type_2330_: *mut leanh::LeanObject,
    mut v_k_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2340_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(
        v_name_2329_,
        v_type_2330_,
        v_k_2331_,
        v___y_2332_,
        v___y_2333_,
        v___y_2334_,
        v___y_2335_,
        v___y_2336_,
        v___y_2337_,
        v___y_2338_,
    );
    return v___x_2340_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___boxed(
    mut v_00_u03b1_2341_: *mut leanh::LeanObject,
    mut v_name_2342_: *mut leanh::LeanObject,
    mut v_type_2343_: *mut leanh::LeanObject,
    mut v_k_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(
        v_00_u03b1_2341_,
        v_name_2342_,
        v_type_2343_,
        v_k_2344_,
        v___y_2345_,
        v___y_2346_,
        v___y_2347_,
        v___y_2348_,
        v___y_2349_,
        v___y_2350_,
        v___y_2351_,
    );
    leanh::lean_dec(v___y_2351_);
    leanh::lean_dec_ref(v___y_2350_);
    leanh::lean_dec(v___y_2349_);
    leanh::lean_dec_ref(v___y_2348_);
    leanh::lean_dec(v___y_2347_);
    leanh::lean_dec_ref(v___y_2346_);
    leanh::lean_dec(v___y_2345_);
    return v_res_2353_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2370_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2371_ =
        leanh::lean_alloc_closure(l_reduceCtorEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2372_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2369_, v___x_2370_, v___x_2371_);
    return v___x_2372_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16____boxed(
    mut v_a_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2374_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
    return v_res_2374_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_()
-> *mut leanh::LeanObject {
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ =
        leanh::lean_alloc_closure(l_reduceCtorEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2376_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2376_, 0, v___x_2375_);
    return v___x_2376_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_()
-> *mut leanh::LeanObject {
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2379_ = 1;
    v___x_2380_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
    v___x_2381_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2378_, v___x_2379_, v___x_2380_);
    return v___x_2381_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(
    mut v_a_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2383_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
    return v_res_2383_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: u8 = 0;
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2386_ = 1;
    v___x_2387_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
    v___x_2388_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2385_, v___x_2386_, v___x_2387_);
    return v___x_2388_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(
    mut v_a_2389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2390_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
    return v_res_2390_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorRecognizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
}